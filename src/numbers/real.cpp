#include "real.hpp"
#include "types.hpp"
#include <cassert>
#include <ostream>

number_base *empty_mpfr = new number_base();
number number::pos_inf, number::neg_inf;

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

number number::operator-() const {
  number_base *r = new number_base;
  mpfr_neg(r->val, data->val, GMP_RNDN);
  return number(r);
}

number const &min(number const &x, number const &y)
{ return (x <= y) ? x : y; }

number const &max(number const &x, number const &y)
{ return (x <= y) ? y : x; }

number_type real_type;

struct real_loader { real_loader(); };
real_loader real_loader_;

real_loader::real_loader() {
  real_type.format = NULL;
  number_base *r = new number_base;
  mpfr_set_inf(r->val, +1);
  number::pos_inf = number(r);
  r = new number_base;
  mpfr_set_inf(r->val, -1);
  number::neg_inf = number(r);
}
