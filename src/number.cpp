#include <sstream>
#include <iostream>
#include "number.hpp"
#include "number_ext.hpp"
#include "ast.hpp"

number_real::number_real(int v) {
  impl_data *d = new impl_data;
  int r = mpfr_set_si(d->val, v, GMP_RNDN);
  assert(r == 0); (void)r;
  data = d;
}

bool number_real::operator<=(number_real const &v) const {
  if (mpfr_nan_p(data->val) || mpfr_nan_p(v.data->val)) return false;
  return mpfr_cmp(data->val, v.data->val) <= 0;
}

number_real const &min(number_real const &x, number_real const &y)
{ return (x <= y) ? x : y; }

number_real const &max(number_real const &x, number_real const &y)
{ return (x <= y) ? y : x; }

number_real to_real(number_float32 const &v) {
  impl_data *res = new impl_data;
  float32_and_float f;
  f.soft = v.value;
  int r = mpfr_set_d(res->val, f.hard, GMP_RNDN);
  assert(r == 0);
  return res;
}

union float32_inside {
  struct {
    unsigned int mantissa:23;
    unsigned int exponent:8;
    unsigned int negative:1;
  };
  float32 value;
};

int ulp_exponent(number_float32 const &v) {
  float32_inside f;
  f.value = v.value;
  int e = f.exponent;
  return ((e == 0) ? -126 : e - 127) - 23;
}

static impl_data *read_number_data(ast_number const &n, int p, mp_rnd_t rnd) {
  impl_data *res = new impl_data;
  mpfr_set_prec(res->val, p);
  if (n.base == 10) {
    std::stringstream s;
    s << n.mantissa << 'e' << n.exponent;
    mpfr_set_str(res->val, s.str().c_str(), 10, rnd);
  } else if (n.base == 2) {
    mpfr_set_str(res->val, n.mantissa.c_str(), 10, rnd);
    mpfr_mul_2si(res->val, res->val, n.exponent, rnd);
  } else {
    assert(n.base == 0);
    mpfr_set_ui(res->val, 0, rnd);
  }
  return res;
}

static int const prec[] = { real_prec, 24, 53, 64, 113 };
static int const min_exp[] = { mpfr_get_emin(), -126, -1022, -16382, -16382 };

impl_data *read_number(ast_number const &n, type_id type, mp_rnd_t rnd) {
  if (n.base == 0) return read_number_data(n, real_prec, rnd);
  impl_data *d;
  int p = prec[type];
  int emin = min_exp[type] - p + 1; // 2^emin == smallest positive floating point number (subnormal)
  for(;;) {
    d = read_number_data(n, p, rnd);
    if (mpfr_sgn(d->val) == 0) return d;
    int e = (d->val[0]._mpfr_exp - 1) - p + 1; // exponent of the least significative bit
    if (e >= emin) return d;
    delete d;
    p += e - emin;
  }
}
