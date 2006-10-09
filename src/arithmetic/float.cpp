#include <algorithm>
#include <cassert>
#include <map>
#include <sstream>
#include "utils.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

extern bool parameter_constrained;

struct float_format: gs_rounding {
  int min_exp, prec;
  virtual int shift_val(int exp, int sz) const { return std::max(min_exp - exp, sz - prec); }
  float_format() {}
  float_format(int e, int p): min_exp(e), prec(p) {}
};

typedef std::map< ast_ident const *, float_format > float_formats;
static float_formats formats;

#define REGISTER_FORMAT(name, e, p) \
  formats.insert(std::make_pair(ast_ident::find(#name), float_format(e, p)))

RUN_ONCE(register_formats) {
  REGISTER_FORMAT(ieee_32 ,   -149,  24);
  REGISTER_FORMAT(ieee_64 ,  -1074,  53);
  REGISTER_FORMAT(ieee_128, -16494, 113);
  REGISTER_FORMAT(x86_80  , -16445,  64);
}

struct float_rounding_class: function_class {
  float_format format;
  direction_type type;
  std::string ident;
  float_rounding_class(float_format const &f, direction_type t, std::string const &i)
    : function_class(UOP_ID, TH_RND | TH_ENF | TH_ABS_EXA_BND | TH_ABS_APX_BND | TH_REL_EXA_ABS | TH_REL_APX_ABS),
      format(f), type(t), ident(i) {}
  virtual interval round                         (interval const &, std::string &) const;
  virtual interval enforce                       (interval const &, std::string &) const;
  virtual interval absolute_error_from_exact_bnd (interval const &, std::string &) const;
  virtual interval absolute_error_from_approx_bnd(interval const &, std::string &) const;
  virtual interval relative_error_from_exact_abs (interval const &, std::string &) const;
  virtual interval relative_error_from_approx_abs(interval const &, std::string &) const;
  virtual std::string name() const { return "rounding_float" + ident; }
};

struct float_rounding_generator: function_generator {
  float_rounding_generator(): function_generator("float") {}
  virtual function_class const *operator()(function_params const &) const;
};

typedef std::map< long long int, float_rounding_class > float_cache;
static float_cache cache;

function_class const *float_rounding_generator::operator()(function_params const &p) const {
  if (p.empty()) return NULL;
  ast_ident const *nf = param_ident(p[0]);
  int nd;
  float_format f;
  if (nf) {
    if (p.size() != 2) return NULL;
    float_formats::const_iterator i = formats.find(nf);
    if (i == formats.end()) return NULL;
    f = i->second;
    nd = 1;
  } else {
    if (p.size() != 3) return NULL;
    if (!param_int(p[0], f.prec) || !param_int(p[1], f.min_exp)) return NULL;
    nd = 2;
  }
  direction_type d = get_direction(p[nd]);
  if (d == ROUND_ARGL) return NULL;
  long long int h = (((long long int)f.min_exp) << 24) | (f.prec << 8) | (int)d;
  float_cache::const_iterator j = cache.find(h);
  if (j != cache.end()) return &j->second;
  std::ostringstream s;
  s << ',' << direction_names[d] << ',' << f.prec << ',' << -f.min_exp;
  j = cache.insert(std::make_pair(h, float_rounding_class(f, d, s.str()))).first;
  return &j->second;
}

static float_rounding_generator dummy;

interval float_rounding_class::enforce(interval const &i, std::string &name) const {
  number a = round_number(lower(i), &format, &float_format::roundUP);
  number b = round_number(upper(i), &format, &float_format::roundDN);
  name = "float_enforce";
  return interval(a, (a <= b) ? b : a);
}

interval float_rounding_class::round(interval const &i, std::string &name) const {
  rounding_fun f = direction_functions[type];
  number a = round_number(lower(i), &format, f);
  number b = round_number(upper(i), &format, f);
  name = "float_round";
  return interval(a, b);
}

static int exponent(number const &n, float_format const &f) {
  mpz_t m;
  int e;
  int s;
  mpz_init(m);
  split_exact(n.data->val, m, e, s);
  if (s == 0) e = f.min_exp;
  else if (e != f.min_exp) {
    e -= f.prec - mpz_sizeinbase(m, 2);
    if (e < f.min_exp) e = f.min_exp;
  }
  mpz_clear(m);
  return e;
}

static bool influenced(number const &n, int e, int e_infl, int infl) {
  mpfr_t x;
  mpfr_init2(x, 150);
  mpfr_set_ui_2exp(x, 1, e, GMP_RNDN);
  if (infl > 0) {
    mpfr_t y;
    mpfr_init(y);
    mpfr_set_ui_2exp(y, 1, e_infl, GMP_RNDN);
    mpfr_add(x, x, y, GMP_RNDD);
    mpfr_clear(y);
  }
  int cmp = mpfr_cmpabs(n.data->val, x);
  mpfr_clear(x);
  return (infl != 1) ? cmp <= 0 : cmp < 0;
}

interval float_rounding_class::absolute_error_from_exact_bnd(interval const &i, std::string &name) const {
  rounding_fun f = direction_functions[type];
  number const &v1 = lower(i), &v2 = upper(i);
  int e1 = exponent(round_number(v1, &format, f), format),
      e2 = exponent(round_number(v2, &format, f), format);
  int e = std::max(e1, e2);
  int e_err = rnd_to_nearest(type) ? e - 1 : e;
  e += format.prec - 1;
  name = "float_absolute";
  if (std::max(e1, e2) > format.min_exp &&
      (v1 >= 0 || influenced(v1, e, e_err - 1, rnd_influence_direction(type, true ))) &&
      (v2 <= 0 || influenced(v2, e, e_err - 1, rnd_influence_direction(type, false)))) {
    name += "_wide";
    --e_err;
  }
  name += ident;
  return from_exponent(e_err, rnd_global_direction_abs(type, i));
}

interval float_rounding_class::absolute_error_from_approx_bnd(interval const &i, std::string &name) const {
  int e1 = exponent(lower(i), format), e2 = exponent(upper(i), format);
  int e_err = std::max(e1, e2);
  name = "float_absolute_inv" + ident;
  if (rnd_to_nearest(type)) return from_exponent(e_err - 1, 0);
  return from_exponent(e_err, rnd_global_direction_abs(type, i));
}

interval float_rounding_class::relative_error_from_exact_abs(interval const &i, std::string &name) const {
  if (parameter_constrained &&
      !is_empty(intersect(i, from_exponent(format.min_exp + format.prec - 1, 0))))
    return interval();
  name = "float_relative" + ident;
  if (rnd_to_nearest(type)) return from_exponent(-format.prec, 0);
  return from_exponent(1 - format.prec, rnd_global_direction_rel(type)); // cannot use i since it is ABS
}

interval float_rounding_class::relative_error_from_approx_abs(interval const &i, std::string &name) const {
  if (parameter_constrained &&
      !is_empty(intersect(i, from_exponent(format.min_exp + format.prec - 1, 0))))
    return interval();
  name = "float_relative_inv" + ident;
  if (rnd_to_nearest(type)) return from_exponent(-format.prec, 0);
  return from_exponent(1 - format.prec, rnd_global_direction_rel(type)); // cannot use i since it is ABS
}

// FIX_OF_FLOAT

REGISTER_SCHEMEX_BEGIN(fix_of_float);
  long min_exp;
  fix_of_float_scheme(predicated_real const &r, long e)
    : proof_scheme(r), min_exp(e) {}
REGISTER_SCHEMEX_END(fix_of_float);

node *fix_of_float_scheme::generate_proof() const {
  return create_theorem(0, NULL, property(real, min_exp), "fix_of_float");
}

preal_vect fix_of_float_scheme::needed_reals() const {
  return preal_vect();
}

proof_scheme *fix_of_float_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  float_rounding_class const *f = dynamic_cast< float_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new fix_of_float_scheme(real, f->format.min_exp);
}

// FLT_OF_FLOAT

REGISTER_SCHEMEX_BEGIN(flt_of_float);
  long prec;
  flt_of_float_scheme(predicated_real const &r, long p)
    : proof_scheme(r), prec(p) {}
REGISTER_SCHEMEX_END(flt_of_float);

node *flt_of_float_scheme::generate_proof() const {
  return create_theorem(0, NULL, property(real, prec), "flt_of_float");
}

preal_vect flt_of_float_scheme::needed_reals() const {
  return preal_vect();
}

proof_scheme *flt_of_float_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FLT) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  float_rounding_class const *f = dynamic_cast< float_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new flt_of_float_scheme(real, f->format.prec);
}

// FLOAT_OF_FIX_FLT

REGISTER_SCHEME_BEGIN(float_of_fix_flt);
  preal_vect needed;
  long min_exp, prec;
  float_of_fix_flt_scheme(ast_real const *r, preal_vect const &v, long e, long p)
    : proof_scheme(r), needed(v), min_exp(e), prec(p) {}
REGISTER_SCHEME_END(float_of_fix_flt);

node *float_of_fix_flt_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  if (hyps[0].cst() < min_exp || hyps[1].cst() > prec) return NULL;
  return create_theorem(2, hyps, property(real, zero()), "float_of_fix_flt");
}

preal_vect float_of_fix_flt_scheme::needed_reals() const {
  return needed;
}

proof_scheme *float_of_fix_flt_scheme::factory(ast_real const *real) {
  ast_real const *holders[2];
  float_rounding_class const *f = dynamic_cast< float_rounding_class const * >(absolute_rounding_error(real, holders));
  if (!f) return NULL;
  preal_vect needed;
  needed.push_back(predicated_real(holders[0], PRED_FIX));
  needed.push_back(predicated_real(holders[0], PRED_FLT));
  return new float_of_fix_flt_scheme(real, needed, f->format.min_exp, f->format.prec);
}
