#include <sstream>
#include <iostream>
#include "number.hpp"
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
