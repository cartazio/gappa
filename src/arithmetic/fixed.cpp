#include <map>
#include <sstream>
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

struct fixed_format: gs_rounding {
  int min_exp;
  virtual int shift_val(int exp, int) const { return min_exp - exp; }
  fixed_format() {}
  fixed_format(int e): min_exp(e) {}
};

struct fixed_rounding_class: function_class {
  fixed_format format;
  direction_type type;
  std::string ident;
  fixed_rounding_class(fixed_format const &f, direction_type t, std::string const &i)
    : function_class(UOP_ID, TH_RND | TH_ABS | (t == ROUND_ZR || t == ROUND_AW ? TH_ABS_EXA_BND | TH_ABS_APX_BND : 0)),
      format(f), type(t), ident(i) {}
  virtual interval round                         (interval const &, std::string &) const;
  virtual interval absolute_error                                  (std::string &) const;
  virtual interval absolute_error_from_exact_bnd (interval const &, std::string &) const;
  virtual interval absolute_error_from_approx_bnd(interval const &, std::string &) const;
  virtual std::string name() const { return "rounding_fixed" + ident; }
};

interval fixed_rounding_class::round(interval const &i, std::string &name) const {
  rounding_fun f = direction_functions[type];
  number a = round_number(lower(i), &format, f);
  number b = round_number(upper(i), &format, f);
  name = "fixed_round";
  return interval(a, b);
}

interval fixed_rounding_class::absolute_error(std::string &name) const {
  name = std::string("fixed_error,") + direction_names[type];
  if (rnd_to_nearest(type)) return from_exponent(format.min_exp - 1, 0);
  return from_exponent(format.min_exp, rnd_global_direction_abs(type));
}

interval fixed_rounding_class::absolute_error_from_exact_bnd(interval const &i, std::string &name) const {
  name = "fixed_error_dir";
  return from_exponent(format.min_exp, rnd_global_direction_abs(type, i));
}

interval fixed_rounding_class::absolute_error_from_approx_bnd(interval const &i, std::string &name) const {
  name = "fixed_error_inv";
  return from_exponent(format.min_exp, rnd_global_direction_abs(type, i));
}

struct fixed_rounding_generator: function_generator {
  fixed_rounding_generator(): function_generator("fixed") {}
  static function_class const *generate(direction_type, int);
  virtual function_class const *operator()(function_params const &) const;
};

typedef std::map< int, fixed_rounding_class > fixed_cache;
static fixed_cache cache;

function_class const *fixed_rounding_generator::generate(direction_type d, int min_exp) {
  if (d == ROUND_ARGL) return NULL;
  int h = (min_exp << 8) | (int)d;
  fixed_cache::const_iterator i = cache.find(h);
  if (i != cache.end()) return &i->second;
  std::ostringstream s;
  s << ',' << direction_names[d] << ',' << min_exp;
  i = cache.insert(std::make_pair(h, fixed_rounding_class(fixed_format(min_exp), d, s.str()))).first;
  return &i->second;
}

function_class const *fixed_rounding_generator::operator()(function_params const &p) const {
  int min_exp;
  if (p.size() != 2 || !param_int(p[0], min_exp)) return NULL;
  return generate(get_direction(p[1]), min_exp);
}

static fixed_rounding_generator dummy;

struct int_rounding_generator: function_generator {
  int_rounding_generator(): function_generator("int") {}
  virtual function_class const *operator()(function_params const &) const;
};

function_class const *int_rounding_generator::operator()(function_params const &p) const {
  if (p.size() != 1) return NULL;
  return fixed_rounding_generator::generate(get_direction(p[0]), 0);
}

static int_rounding_generator dummy2;

// FIX_OF_FIXED
REGISTER_SCHEME_BEGIN(fix_of_fixed);
  fixed_rounding_class const *rnd;
  fix_of_fixed_scheme(predicated_real const &r, fixed_rounding_class const *f)
    : proof_scheme(r), rnd(f) {}
REGISTER_SCHEME_END_PREDICATE(fix_of_fixed);

node *fix_of_fixed_scheme::generate_proof() const {
  return create_theorem(0, NULL, property(real, rnd->format.min_exp), "fix_of_fixed");
}

preal_vect fix_of_fixed_scheme::needed_reals() const {
  return preal_vect();
}

proof_scheme *fix_of_fixed_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  fixed_rounding_class const *f = dynamic_cast< fixed_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new fix_of_fixed_scheme(real, f);
}

// FIXED_OF_FIX
REGISTER_SCHEME_BEGIN(fixed_of_fix);
  predicated_real fixval;
  long min_exp;
  fixed_of_fix_scheme(ast_real const *r, predicated_real const &v, long e)
    : proof_scheme(r), fixval(v), min_exp(e) {}
REGISTER_SCHEME_END(fixed_of_fix);

node *fixed_of_fix_scheme::generate_proof() const {
  node *n = find_proof(fixval);
  if (!n) return NULL;
  property const &hyp = n->get_result();
  if (hyp.cst() < min_exp) return NULL;
  return create_theorem(1, &hyp, property(real, zero()), "fixed_of_fix");
}

preal_vect fixed_of_fix_scheme::needed_reals() const {
  return preal_vect(1, fixval);
}

proof_scheme *fixed_of_fix_scheme::factory(ast_real const *real) {
  ast_real const *holders[2];
  fixed_rounding_class const *f = dynamic_cast< fixed_rounding_class const * >(absolute_rounding_error(real, holders));
  if (!f) return NULL;
  return new fixed_of_fix_scheme(real, predicated_real(holders[0], PRED_FIX), f->format.min_exp);
}

// BND_OF_BND_FIX
REGISTER_SCHEME_BEGIN(bnd_of_bnd_fix);
  preal_vect needed;
  bnd_of_bnd_fix_scheme(preal_vect const &v)
    : proof_scheme(v[0]), needed(v) {}
REGISTER_SCHEME_END(bnd_of_bnd_fix);

node *bnd_of_bnd_fix_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  fixed_format format(hyps[1].cst());
  interval const &i = hyps[0].bnd();
  number a = round_number(lower(i), &format, &fixed_format::roundUP);
  number b = round_number(upper(i), &format, &fixed_format::roundDN);
  property res(real, interval(a, (a <= b) ? b : a));
  return create_theorem(2, hyps, res, "bnd_of_bnd_fix");
}

preal_vect bnd_of_bnd_fix_scheme::needed_reals() const {
  return needed;
}

extern bool is_constant(ast_real const *);

proof_scheme *bnd_of_bnd_fix_scheme::factory(ast_real const *real)
{
  if (is_constant(real)) return NULL;
  real_op const *p = boost::get< real_op const >(real);
  if (p && p->type == UOP_ABS) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(real, PRED_BND));
  hyps.push_back(predicated_real(real, PRED_FIX));
  return new bnd_of_bnd_fix_scheme(hyps);
}

// FIX_FIXED_OF_FIX

REGISTER_SCHEME_BEGIN(fix_fixed_of_fix);
  predicated_real needed;
  fix_fixed_of_fix_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r), needed(n) {}
REGISTER_SCHEME_END_PREDICATE(fix_fixed_of_fix);

node *fix_fixed_of_fix_scheme::generate_proof() const {
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &res = n->get_result();
  return create_theorem(1, &res, property(real, res.cst()), "fix_fixed_of_fix");
}

preal_vect fix_fixed_of_fix_scheme::needed_reals() const {
  return preal_vect(1, needed);
}

proof_scheme *fix_fixed_of_fix_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  fixed_rounding_class const *f = dynamic_cast< fixed_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new fix_fixed_of_fix_scheme(real, predicated_real(r->ops[0], PRED_FIX));
}

// FLT_FIXED_OF_FLT

REGISTER_SCHEME_BEGIN(flt_fixed_of_flt);
  predicated_real needed;
  flt_fixed_of_flt_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r), needed(n) {}
REGISTER_SCHEME_END_PREDICATE(flt_fixed_of_flt);

node *flt_fixed_of_flt_scheme::generate_proof() const {
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &res = n->get_result();
  return create_theorem(1, &res, property(real, res.cst()), "flt_fixed_of_flt");
}

preal_vect flt_fixed_of_flt_scheme::needed_reals() const {
  return preal_vect(1, needed);
}

proof_scheme *flt_fixed_of_flt_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FLT) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  fixed_rounding_class const *f = dynamic_cast< fixed_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new flt_fixed_of_flt_scheme(real, predicated_real(r->ops[0], PRED_FLT));
}
