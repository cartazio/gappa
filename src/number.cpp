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

int exponent(number_float32 const &v) {
  float32_inside f;
  f.value = v.value;
  int e = f.exponent;
  return (e == 0) ? -126 : e - 127;
}

union float64_inside {
  struct {
    unsigned long long int mantissa:52;
    unsigned long long int exponent:11;
    unsigned long long int negative:1;
  };
  float64 value;
};

int exponent(number_float64 const &v) {
  float64_inside f;
  f.value = v.value;
  int e = f.exponent;
  return (e == 0) ? -1022 : e - 1023;
}

union floatx80_inside {
  struct {
    unsigned int exponent:15;
    unsigned int negative:1;
  };
  unsigned int value;
};

int exponent(number_floatx80 const &v) {
  floatx80_inside f;
  f.value = v.value.high;
  int e = f.exponent;
  return (e == 0) ? -16382 : e - 16383;
}

union float128_inside {
  struct {
    unsigned long long int mantissa2:48;
    unsigned long long int exponent:15;
    unsigned long long int negative:1;
  };
  unsigned long long int value;
};

int exponent(number_float128 const &v) {
  float128_inside f;
  f.value = v.value.high;
  int e = f.exponent;
  return (e == 0) ? -16382 : e - 16383;
}

int ulp_exponent(number_float32 const &v) { return exponent(v) - 23; }
int ulp_exponent(number_float64 const &v) { return exponent(v) - 52; }
int ulp_exponent(number_floatx80 const &v) { return exponent(v) - 63; }
int ulp_exponent(number_float128 const &v) { return exponent(v) - 112; }

void split(number_float32 &u, number_float32 &v) {
  static float32 half = 126 << 23;
  float32 m = float32_mul(float32_add(u.value, v.value), half);
  if (m == u.value || m == v.value) return;
  float32 n = m + 1; // n is near m since m != -1 (NaN)
  if (m >= 0) { u.value = n; v.value = m; } else { u.value = m; v.value = n; }
}

void split(number_float64 &u, number_float64 &v) { throw; u = v; }
void split(number_floatx80 &u, number_floatx80 &v) { throw; u = v; }
void split(number_float128 &u, number_float128 &v) { throw; u = v; }

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
