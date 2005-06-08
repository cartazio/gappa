#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"
#include <algorithm>

enum rounding_type { ROUND_UP, ROUND_DN, ROUND_ZR, ROUND_NE };

static rounding_fun roundings[4] = {
  &float_format::roundU,
  &float_format::roundD,
  &float_format::roundZ,
  &float_format::roundNE
};

static float_format formats[4] = {
  { min_exp: -149,   prec: 24  },
  { min_exp: -1074,  prec: 53  },
  { min_exp: -16445, prec: 64  },
  { min_exp: -16494, prec: 113 }
};

struct float_rounding_class: rounding_class {
  float_format const *format;
  rounding_type type;
  char const *ident;
  float_rounding_class(float_format const *f, rounding_type t, char const *i);
  virtual interval round                      (interval const &, std::string &) const;
  virtual interval enforce                    (interval const &, std::string &) const;
  virtual interval absolute_error_from_real   (interval const &, std::string &) const;
  virtual interval relative_error_from_real   (interval const &, std::string &) const;
  virtual interval absolute_error_from_rounded(interval const &, std::string &) const;
  virtual interval relative_error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const { return std::string("float") + ident; }
};

float_rounding_class::float_rounding_class(float_format const *f, rounding_type t, char const *i)
  : format(f), type(t), ident(i)
{
  ast_ident *n = ast_ident::find(std::string("float") + i);
  n->id_type = REAL_RND;
  n->rnd = this;
}


static float_rounding_class classes[4][4] = {
  { float_rounding_class(&formats[0], ROUND_UP,  "32up"),
    float_rounding_class(&formats[0], ROUND_DN,  "32dn"),
    float_rounding_class(&formats[0], ROUND_ZR,  "32zr"),
    float_rounding_class(&formats[0], ROUND_NE,  "32ne") },
  { float_rounding_class(&formats[1], ROUND_UP,  "64up"),
    float_rounding_class(&formats[1], ROUND_DN,  "64dn"),
    float_rounding_class(&formats[1], ROUND_ZR,  "64zr"),
    float_rounding_class(&formats[1], ROUND_NE,  "64ne") },
  { float_rounding_class(&formats[2], ROUND_UP,  "80up"),
    float_rounding_class(&formats[2], ROUND_DN,  "80dn"),
    float_rounding_class(&formats[2], ROUND_ZR,  "80zr"),
    float_rounding_class(&formats[2], ROUND_NE,  "80ne") },
  { float_rounding_class(&formats[3], ROUND_UP, "128up"),
    float_rounding_class(&formats[3], ROUND_DN, "128dn"),
    float_rounding_class(&formats[3], ROUND_ZR, "128zr"),
    float_rounding_class(&formats[3], ROUND_NE, "128ne") }
};

interval float_rounding_class::enforce(interval const &i, std::string &name) const {
  number a = round_number(lower(i), format, &float_format::roundU);
  number b = round_number(upper(i), format, &float_format::roundD);
  name = std::string("float") + ident + "_enforce";
  if (!(a <= b)) return interval();
  return interval(a, b);
}

interval float_rounding_class::round(interval const &i, std::string &name) const {
  rounding_fun f = roundings[type];
  number a = round_number(lower(i), format, f);
  number b = round_number(upper(i), format, f);
  name = std::string("float") + ident + "_round";
  return interval(a, b);
}

static int exponent(number const &n, float_format const *f) {
  mpz_t m;
  int e;
  int s;
  mpz_init(m);
  split_exact(n.data->val, m, e, s);
  if (s == 0) e = f->min_exp;
  else if (e != f->min_exp) {
    e -= f->prec - mpz_sizeinbase(m, 2);
    if (e < f->min_exp) e = f->min_exp;
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
  rounding_fun f = roundings[type];
  number const &v1 = lower(i), &v2 = upper(i);
  int e1 = exponent(round_number(v1, format, f), format),
      e2 = exponent(round_number(v2, format, f), format);
  int e = std::max(e1, e2);
  int e_err = type == ROUND_NE ? e - 1 : e;
  e += format->prec - 1;
  name = std::string("float") + ident + "_absolute";
  if (influenced(v1, e, e_err - 1, type != ROUND_DN || mpfr_sgn(v1.data->val) >= 0) &&
      influenced(v2, e, e_err - 1, type != ROUND_UP || mpfr_sgn(v1.data->val) <= 0)) {
    name += "_wide";
    --e_err;
  }
  return from_exponent(e_err, type == ROUND_UP ? 1 : (type == ROUND_DN ? -1 : 0));
}

interval float_rounding_class::absolute_error_from_rounded(interval const &i, std::string &name) const {
  int e1 = exponent(lower(i), format), e2 = exponent(upper(i), format);
  int e_err = std::max(e1, e2);
  if (type == ROUND_NE) --e_err;
  name = std::string("float") + ident + "_absolute_inv";
  return from_exponent(e_err, type == ROUND_UP ? 1 : (type == ROUND_DN ? -1 : 0));
}

interval float_rounding_class::relative_error_from_real(interval const &i, std::string &name) const {
  if (!is_empty(intersect(i, from_exponent(format->min_exp + format->prec - 1, 0))))
    return interval();
  name = std::string("float") + ident + "_relative";
  return from_exponent(type == ROUND_NE ? -format->prec : 1 - format->prec,
                       type == ROUND_ZR ? -1 : 0);
}

interval float_rounding_class::relative_error_from_rounded(interval const &i, std::string &name) const {
  if (!is_empty(intersect(i, from_exponent(format->min_exp + format->prec - 1, 0))))
    return interval();
  name = std::string("float") + ident + "_relative_inv";
  return from_exponent(type == ROUND_NE ? -format->prec : 1 - format->prec,
                       type == ROUND_ZR ? -1 : 0);
}

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
  rounded_real const *rr = boost::get< rounded_real const >(o1->ops[0]);
  if (!rr) return false;
  float_rounding_class const *fr = dynamic_cast< float_rounding_class const * >(rr->rounding);
  if (!fr) return false;
  real_op const *o2 = boost::get< real_op const >(rr->rounded);
  if (!o2 || !(o2->type == BOP_ADD || o2->type == BOP_SUB)) return false;
  if (r1) *r1 = o1->ops[0];
  if (r2) *r2 = normalize(ast_real(real_op(rr->rounded, BOP_SUB, o1->ops[1])));
  if (a) *a = o2->ops[0];
  if (b) *b = o2->ops[1];
  if (ff) *ff = fr->format;
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
  rounded_real const *rr = boost::get< rounded_real const >(r);
  if (!rr) return NULL;
  float_rounding_class const *fr = dynamic_cast< float_rounding_class const * >(rr->rounding);
  if (!fr) return NULL;
  if (contains_zero(bnd)) e = fr->format->min_exp;
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
  int e = std::max(exponent(lower(res1.bnd), f), exponent(upper(res1.bnd), f));
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
