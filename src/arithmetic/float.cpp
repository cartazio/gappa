#include <algorithm>
#include <cassert>
#include <map>
#include <sstream>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

struct float_format: gs_rounding {
  int min_exp, prec;
  virtual int shift_val(int exp, int sz) const { return std::max(min_exp - exp, sz - prec); }
  float_format() {}
  float_format(int e, int p): min_exp(e), prec(p) {}
};

typedef std::map< ast_ident const *, float_format > float_formats;
static float_formats formats;

struct float_format_register {
  float_format_register(char const *name, int e, int p) {
    formats.insert(std::make_pair(ast_ident::find(name), float_format(e, p)));
  }
};

#define REGISTER_FORMAT(name, e, p) \
  static float_format_register name##_format_register(#name, e, p)

REGISTER_FORMAT(ieee_32 ,   -149,  24);
REGISTER_FORMAT(ieee_64 ,  -1074,  53);
REGISTER_FORMAT(ieee_128, -16494, 113);
REGISTER_FORMAT(x86_80  , -16445,  64);

struct float_rounding_class: function_class {
  float_format format;
  direction_type type;
  std::string ident;
  float_rounding_class(float_format const &f, direction_type t, std::string const &i)
    : function_class(UOP_ID, TH_RND | TH_ENF | TH_ABS_REA | TH_ABS_RND | TH_REL_REA | TH_REL_RND),
      format(f), type(t), ident(i) {}
  virtual interval round                      (interval const &, std::string &) const;
  virtual interval enforce                    (interval const &, std::string &) const;
  virtual interval absolute_error_from_real   (interval const &, std::string &) const;
  virtual interval relative_error_from_real   (interval const &, std::string &) const;
  virtual interval absolute_error_from_rounded(interval const &, std::string &) const;
  virtual interval relative_error_from_rounded(interval const &, std::string &) const;
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
  number a = round_number(lower(i), &format, &float_format::roundU);
  number b = round_number(upper(i), &format, &float_format::roundD);
  name = "float_enforce" + ident;
  return interval(a, (a <= b) ? b : a);
}

interval float_rounding_class::round(interval const &i, std::string &name) const {
  rounding_fun f = direction_functions[type];
  number a = round_number(lower(i), &format, f);
  number b = round_number(upper(i), &format, f);
  name = "float_round" + ident;
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

static bool influenced(number const &n, int e, int e_infl, bool infl) {
  mpfr_t x, y;
  mpfr_init2(x, 150);
  mpfr_set_ui_2exp(x, 1, e, GMP_RNDN);
  if (infl) {
    mpfr_init(y);
    mpfr_set_ui_2exp(y, 1, e_infl, GMP_RNDN);
    mpfr_add(x, x, y, GMP_RNDD);
    mpfr_clear(y);
  }
  int cmp = mpfr_cmpabs(n.data->val, x);
  mpfr_clear(x);
  return cmp <= 0;
}

interval float_rounding_class::absolute_error_from_real(interval const &i, std::string &name) const {
  rounding_fun f = direction_functions[type];
  number const &v1 = lower(i), &v2 = upper(i);
  int e1 = exponent(round_number(v1, &format, f), format),
      e2 = exponent(round_number(v2, &format, f), format);
  int e = std::max(e1, e2);
  int e_err = type == ROUND_NE ? e - 1 : e;
  e += format.prec - 1;
  name = "float_absolute";
  if (influenced(v1, e, e_err - 1, type != ROUND_DN || mpfr_sgn(v1.data->val) >= 0) &&
      influenced(v2, e, e_err - 1, type != ROUND_UP || mpfr_sgn(v1.data->val) <= 0)) {
    name += "_wide";
    --e_err;
  }
  name += ident;
  return from_exponent(e_err, type == ROUND_UP ? 1 : (type == ROUND_DN ? -1 : 0));
}

interval float_rounding_class::absolute_error_from_rounded(interval const &i, std::string &name) const {
  int e1 = exponent(lower(i), format), e2 = exponent(upper(i), format);
  int e_err = std::max(e1, e2);
  name = "float_absolute_inv" + ident;
  if (type == ROUND_DN || type == ROUND_ZR && lower(i) > 0) return from_exponent(e_err, -1);
  if (type == ROUND_UP || type == ROUND_ZR && upper(i) < 0) return from_exponent(e_err, +1);
  return from_exponent(type == ROUND_ZR ? e_err : e_err - 1, 0);
}

interval float_rounding_class::relative_error_from_real(interval const &i, std::string &name) const {
  if (!is_empty(intersect(i, from_exponent(format.min_exp + format.prec - 1, 0))))
    return interval();
  name = "float_relative" + ident;
  return from_exponent(type == ROUND_NE ? -format.prec : 1 - format.prec,
                       type == ROUND_ZR ? -1 : 0);
}

interval float_rounding_class::relative_error_from_rounded(interval const &i, std::string &name) const {
  if (!is_empty(intersect(i, from_exponent(format.min_exp + format.prec - 1, 0))))
    return interval();
  name = "float_relative_inv" + ident;
  return from_exponent(type == ROUND_NE ? -format.prec : 1 - format.prec,
                       type == ROUND_ZR ? -1 : 0);
}

/*
struct sterbenz_scheme: proof_scheme {
  sterbenz_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
  static proof_scheme *factory(ast_real const *);
};

static bool sterbenz_decomposition(ast_real const *real, ast_real const **r1, ast_real const **r2,
                                   ast_real const **a, ast_real const **b, float_format const **ff) {
  real_op const *o1 = boost::get< real_op const >(real);
  if (!o1 || o1->type != BOP_SUB) return false;
  real_op const *rr = boost::get< real_op const >(o1->ops[0]);
  if (!rr) return false;
  float_rounding_class const *fr = dynamic_cast< float_rounding_class const * >(rr->fun);
  if (!fr) return false;
  real_op const *o2 = boost::get< real_op const >(rr->ops[0]);
  if (!o2 || !(o2->type == BOP_ADD || o2->type == BOP_SUB)) return false;
  if (r1) *r1 = o1->ops[0];
  if (r2) *r2 = normalize(ast_real(real_op(rr->ops[0], BOP_SUB, o1->ops[1])));
  if (a) *a = o2->ops[0];
  if (b) *b = o2->ops[1];
  if (ff) *ff = &fr->format;
  return true;
}

static node *sterbenz_exponent(ast_real const *r, int &e) {
  node *n = find_proof(r);
  if (!n) return NULL;
  interval const &bnd = n->get_result().bnd;
  number const &l = lower(bnd), &u = upper(bnd);
  if (l == u) {
    int s;
    mpz_t m;
    mpz_init(m);
    split_exact(l.data->val, m, e, s);
    mpz_clear(m);
    return n;
  }
  real_op const *rr = boost::get< real_op const >(r);
  if (!rr) return NULL;
  float_rounding_class const *fr = dynamic_cast< float_rounding_class const * >(rr->fun);
  if (!fr) return NULL;
  if (contains_zero(bnd)) e = fr->format.min_exp;
  else e = std::min(exponent(l, fr->format), exponent(u, fr->format));
  return n;
}

node *sterbenz_scheme::generate_proof() const {
  ast_real const *r1, *r2, *ra, *rb; float_format const *f;
  bool b = sterbenz_decomposition(real, &r1, &r2, &ra, &rb, &f);
  assert(b);
  int ea, eb;
  node *na = sterbenz_exponent(ra, ea), *nb = sterbenz_exponent(rb, eb);
  node *n1 = find_proof(r1), *n2 = find_proof(r2);
  if (!n1 || !n2 || !na || !nb) return NULL;
  property const &res1 = n1->get_result(), &res2 = n2->get_result(), &resa = na->get_result(), &resb = nb->get_result();
  int e = std::max(exponent(lower(res1.bnd), *f), exponent(upper(res1.bnd), *f));
  if (ea < e || eb < e) return NULL;
  property res[] = { resa, resb, res1, res2 };
  return create_theorem(4, res, property(real, res2.bnd), "sterbenz");
}

ast_real_vect sterbenz_scheme::needed_reals() const {
  ast_real_vect res(4);
  bool b = sterbenz_decomposition(real, &res[0], &res[1], &res[2], &res[3], NULL);
  assert(b);
  return res;
}

proof_scheme *sterbenz_scheme::factory(ast_real const *real) {
  bool b = sterbenz_decomposition(real, NULL, NULL, NULL, NULL, NULL);
  if (!b) return NULL;
  return new sterbenz_scheme(real);
}

static scheme_register sterbenz_scheme_register(&sterbenz_scheme::factory);
*/
