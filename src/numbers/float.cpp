#include "parser/ast.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include <algorithm>

enum rounding_type { ROUND_UP, ROUND_DN, ROUND_ZR, ROUND_CE };

static rounding_fun roundings[4] = {
  &float_format::roundU,
  &float_format::roundD,
  &float_format::roundZ,
  &float_format::roundCE
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
  virtual interval bound(interval const &, std::string &) const;
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
    float_rounding_class(&formats[0], ROUND_CE,  "32ce") },
  { float_rounding_class(&formats[1], ROUND_UP,  "64up"),
    float_rounding_class(&formats[1], ROUND_DN,  "64dn"),
    float_rounding_class(&formats[1], ROUND_ZR,  "64zr"),
    float_rounding_class(&formats[1], ROUND_CE,  "64ce") },
  { float_rounding_class(&formats[2], ROUND_UP,  "80up"),
    float_rounding_class(&formats[2], ROUND_DN,  "80dn"),
    float_rounding_class(&formats[2], ROUND_ZR,  "80zr"),
    float_rounding_class(&formats[2], ROUND_CE,  "80ce") },
  { float_rounding_class(&formats[3], ROUND_UP, "128up"),
    float_rounding_class(&formats[3], ROUND_DN, "128dn"),
    float_rounding_class(&formats[3], ROUND_ZR, "128zr"),
    float_rounding_class(&formats[3], ROUND_CE, "128ce") }
};

interval float_rounding_class::bound(interval const &i, std::string &name) const {
  rounding_fun f = roundings[type];
  number a = round_number(lower(i), format, f);
  number b = round_number(upper(i), format, f);
  name = std::string("float") + ident + "_bound";
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

static bool influenced(number const &n, int e, int e_infl, bool strict) {
  mpfr_t x, y;
  mpfr_init2(x, 150);
  mpfr_init(y);
  mpfr_set_ui_2exp(x, 1, e, GMP_RNDN);
  mpfr_set_ui_2exp(y, 1, e_infl, GMP_RNDN);
  mpfr_add(x, x, y, GMP_RNDD);
  mpfr_clear(y);
  int cmp = mpfr_cmpabs(n.data->val, x);
  mpfr_clear(x);
  return cmp < 0 || (!strict && cmp == 0);
}

interval float_rounding_class::absolute_error_from_real(interval const &i, std::string &name) const {
  rounding_fun f = roundings[type];
  int e1 = exponent(round_number(lower(i), format, f), format),
      e2 = exponent(round_number(upper(i), format, f), format);
  int e = std::max(e1, e2);
  int e_err = type == ROUND_CE ? e - 1 : e;
  e += format->prec - 1;
  name = std::string("float") + ident + "_error";
  if (influenced(lower(i), e, e_err, false) && influenced(upper(i), e, e_err, false)) {
    name += "_wide";
    --e_err;
  }
  return from_exponent(e_err, type == ROUND_UP ? 1 : (type == ROUND_DN ? -1 : 0));
}

interval float_rounding_class::absolute_error_from_rounded(interval const &i, std::string &name) const {
  int e1 = exponent(lower(i), format), e2 = exponent(upper(i), format);
  int e_err = std::max(e1, e2);
  if (type == ROUND_CE) --e_err;
  name = std::string("float") + ident + "_error_inv";
  return from_exponent(e_err, type == ROUND_UP ? 1 : (type == ROUND_DN ? -1 : 0));
}

interval float_rounding_class::relative_error_from_rounded(interval const &i, std::string &name) const {
  name = std::string("float") + ident + "_relative";
  return from_exponent(type == ROUND_CE ? -format->prec : 1 - format->prec,
                       type == ROUND_ZR ? -1 : 0);
}

interval float_rounding_class::relative_error_from_real(interval const &i, std::string &name) const {
  name = std::string("float") + ident + "_relative";
  return from_exponent(type == ROUND_CE ? -format->prec : 1 - format->prec,
                       type == ROUND_ZR ? -1 : 0);
}
