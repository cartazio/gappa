#include "real.hpp"

number_real::number_real(int v) {
  impl_data *d = new impl_data;
  int r = mpfr_set_si(d->val, v, GMP_RNDN);
  assert(r == 0); (void)r;
  data = d;
}

bool number_real::operator<=(number_real const &v) const {
  if (mpfr_nan_p(data->val) || mpfr_nan_p(v.data->val)) return false;
  return mpfr_cmp(data->val, v.data->val) <= 0;
  //return mpfr_lessequal_p(data->val, v.data->val);
}

bool number_real::operator==(number_real const &v) const {
  if (mpfr_nan_p(data->val) || mpfr_nan_p(v.data->val)) return false;
  return mpfr_cmp(data->val, v.data->val) == 0;
  //return mpfr_equal_p(data->val, v.data->val);
}

number_real const &min(number_real const &x, number_real const &y)
{ return (x <= y) ? x : y; }

number_real const &max(number_real const &x, number_real const &y)
{ return (x <= y) ? y : x; }

interval from_exponent(int exp, int rnd) {
  impl_data *l = new impl_data, *u = new impl_data;
  if (rnd == 0) {
    mpfr_set_ui(u->val, 1, GMP_RNDN);
    mpfr_mul_2si(u->val, u->val, exp - 1, GMP_RNDN);
    mpfr_neg(l->val, u->val, GMP_RNDN);
  } else if (rnd < 0) {
    mpfr_set_si(l->val, -1, GMP_RNDN);
    mpfr_set_ui(u->val, 0, GMP_RNDN);
    mpfr_mul_2si(l->val, l->val, exp, GMP_RNDN);
  } else {
    mpfr_set_ui(l->val, 0, GMP_RNDN);
    mpfr_set_ui(u->val, 1, GMP_RNDN);
    mpfr_mul_2si(u->val, u->val, exp, GMP_RNDN);
  }
  return interval(interval_real, new _interval_real(number_real(l), number_real(u)));
}

#define pcast(p) static_cast< _interval_real * >(p)
#define cast(p) *static_cast< _interval_real * >(p)
#define gen(p) new _interval_real(p)

static void *create() { return new _interval_real; }
static void destroy(void *v) { delete pcast(v); }
static void *clone(void *v) { return gen(cast(v)); }
static void *add(void *u, void *v) { return gen(cast(u) + cast(v)); }
static void *sub(void *u, void *v) { return gen(cast(u) - cast(v)); }
static void *mul(void *u, void *v) { return gen(cast(u) * cast(v)); }
static void *div(void *u, void *v) { return gen(cast(u) / cast(v)); }
static bool subset(void *u, void *v) { return subset(cast(u), cast(v)); }
static bool singleton(void *v) { return singleton(cast(v)); }

interval_description interval_real_desc =
  { create: &create, destroy: &destroy, clone: &clone,
    add: &add, sub: &sub, mul: &mul, div: &div,
    subset: &subset, singleton: &singleton };

interval_description *interval_real = &interval_real_desc;
