#include "real.hpp"
#include "types.hpp"
#include <cassert>
#include <ostream>

number::number(int v) {
  number_base *d = new number_base;
  int r = mpfr_set_si(d->val, v, GMP_RNDN);
  assert(r == 0); (void)r;
  data = d;
}

number &number::operator=(number const &v) {
  if (this != &v) {
    data->destroy();
    number_base const *d = v.data->clone();
    data = d;
  }
  return *this;
}

bool number::operator<=(number const &v) const {
  if (mpfr_nan_p(data->val) || mpfr_nan_p(v.data->val)) return false;
  return mpfr_cmp(data->val, v.data->val) <= 0;
  //return mpfr_lessequal_p(data->val, v.data->val);
}

bool number::operator==(number const &v) const {
  if (mpfr_nan_p(data->val) || mpfr_nan_p(v.data->val)) return false;
  return mpfr_cmp(data->val, v.data->val) == 0;
  //return mpfr_equal_p(data->val, v.data->val);
}

bool number::operator!=(number const &v) const {
  if (mpfr_nan_p(data->val) || mpfr_nan_p(v.data->val)) return false;
  return mpfr_cmp(data->val, v.data->val) != 0;
}

number_base *number::unique() const {
  if (data->ref_counter.nb != 1) {
    number_base *d = new number_base;
    mpfr_set_prec(d->val, mpfr_get_prec(data->val));
    mpfr_set(d->val, data->val, GMP_RNDN);
    data->destroy();
    data = d;
  }
  return const_cast< number_base * >(data);
}

number const &min(number const &x, number const &y)
{ return (x <= y) ? x : y; }

number const &max(number const &x, number const &y)
{ return (x <= y) ? y : x; }

number_type real_type;

struct real_loader {
  real_loader() { real_type.format = NULL; }
  static real_loader loader;
};
