#include "real.hpp"
#include <ostream>

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

interval_real from_exponent(int exp, int rnd) {
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
  return interval_real(new _interval_real(number_real(l), number_real(u)));
}

std::ostream &operator<<(std::ostream &, number_real const &);

template<class T, class Policies>
std::ostream &operator<<(std::ostream &stream, boost::numeric::interval<T, Policies> const &value) {
  if (empty(value)) {
    return stream << "[]";
  } else if (singleton(value)) {
    return stream << '[' << lower(value) << ']';
  } else {
    return stream << '[' << lower(value) << ", " << upper(value) << ']';
  }
}


#define pcast(p) static_cast< _interval_real * >(p)
#define cast(p) *static_cast< _interval_real * >(p)
#define gen(p) new _interval_real(p)

static void *create() { return new _interval_real; }
static void destroy(void *v) { delete pcast(v); }
static void *clone(void *v) { return gen(cast(v)); }
static bool subset(void *u, void *v) { return subset(cast(u), cast(v)); }
static bool singleton(void *v) { return singleton(cast(v)); }
static bool zero(void *v) { return in_zero(cast(v)); }
static void *hull(void *u, void *v) { return gen(hull(cast(u), cast(v))); }
static void *intersect(void *u, void *v) { return gen(intersect(cast(u), cast(v))); }
static void output(std::ostream &s, void *v) { s << cast(v); }

interval_description interval_real_desc_ =
  { create: &create, destroy: &destroy, clone: &clone,
    subset: &subset, singleton: &singleton, in_zero: &zero,
    to_real: 0, hull: &hull, intersect: &intersect, split: 0, output: &output };

interval_description *interval_real_desc = &interval_real_desc_;

interval_real operator+(interval_real const &u, interval_real const &v)
{ return interval_real(gen(cast(u.ptr) + cast(v.ptr))); }
interval_real operator-(interval_real const &u, interval_real const &v)
{ return interval_real(gen(cast(u.ptr) - cast(v.ptr))); }
interval_real operator*(interval_real const &u, interval_real const &v)
{ return interval_real(gen(cast(u.ptr) * cast(v.ptr))); }
interval_real operator/(interval_real const &u, interval_real const &v)
{ return interval_real(gen(cast(u.ptr) / cast(v.ptr))); }
