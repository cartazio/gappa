#include "interval.hpp"
#include "interval_arith.hpp"
#include "interval_utility.hpp"
#include "real.hpp"
#include <cassert>
#include <boost/numeric/interval/arith.hpp>
#include <boost/numeric/interval/arith2.hpp>
#include <boost/numeric/interval/checking.hpp>
#include <boost/numeric/interval/interval.hpp>
#include <boost/numeric/interval/policies.hpp>
#include <boost/numeric/interval/rounded_arith.hpp>
#include <boost/numeric/interval/utility.hpp>

class real_policies {
  typedef number T;
public:
# define RES(name) number_base *name = new number_base()
  struct rounding {
    static T conv_down(int v)		{ RES(w); mpfr_set_si(w->val, v, GMP_RNDD); return T(w); }
    static T conv_up  (int v)		{ RES(w); mpfr_set_si(w->val, v, GMP_RNDU); return T(w); }
    static T conv_down(T const &v)	{ return v; }
    static T conv_up  (T const &v)	{ return v; }
    static T opp_down(T const &v)	{ RES(w); mpfr_neg(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T opp_up  (T const &v)	{ RES(w); mpfr_neg(w->val, v.data->val, GMP_RNDU); return T(w); }
    static T sqrt_down(T const &v)	{ RES(w); mpfr_sqrt(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T sqrt_up  (T const &v)	{ RES(w); mpfr_sqrt(w->val, v.data->val, GMP_RNDU); return T(w); }
#   define BINARY_FUNC(name) \
    static T name##_down(T const &x, T const &y) \
    { RES(z); mpfr_##name(z->val, x.data->val, y.data->val, GMP_RNDD); return T(z); } \
    static T name##_up  (T const &x, T const &y) \
    { RES(z); mpfr_##name(z->val, x.data->val, y.data->val, GMP_RNDU); return T(z); }
    BINARY_FUNC(add);
    BINARY_FUNC(sub);
    BINARY_FUNC(mul);
    BINARY_FUNC(div);
#   undef BINARY_FUNC
    static T median(T const &x, T const &y) {
      RES(w); mpfr_add(w->val, x.data->val, y.data->val, GMP_RNDN);
      mpfr_div_2ui(w->val, w->val, 1, GMP_RNDN); return T(w);
    }
    typedef rounding unprotected_rounding;
  };
  struct checking {
    static bool is_nan(int) { return false; }
    static bool is_nan(double v) { return (v != v); }
    static bool is_nan(T const &v) { return mpfr_nan_p(v.data->val); }
    static T empty_lower() { return T(); }
    static T empty_upper() { return T(); }
    static T pos_inf() { return T::pos_inf; }
    static T neg_inf() { return T::neg_inf; }
    static T nan() { RES(w); return T(w); }
    static bool is_empty(T const &x, T const &y) { return !(x <= y); }
  };
# undef RES
};

typedef boost::numeric::interval< number, real_policies > _interval_base;

class interval_base {
  interval_base(interval_base const &i);
 public:
  _interval_base value;
  mutable ref_counter_t ref_counter;
  interval_base() {}
  interval_base(_interval_base const &v): value(v) {}
  interval_base const *clone() const { ref_counter.incr(); return this; }
  void destroy() const { if (ref_counter.decr()) delete this; }
  friend class interval;
};

interval_base *interval::unique() const {
  if (base->ref_counter.nb != 1) {
    interval_base *b = new interval_base(base->value);
    base->destroy();
    base = b;
  }
  return const_cast< interval_base * >(base);
}

interval::interval(interval const &i): base(i.base ? i.base->clone() : 0) {}
interval::~interval() { if (base) base->destroy(); }

interval &interval::operator=(interval const &i) {
  if (this != &i) {
    if (base) base->destroy();
    base = i.base ? i.base->clone() : 0;
  }
  return *this;
}

interval::interval(number const &l, number const &u) {
  base = new interval_base(_interval_base(l, u));
}

#define plip(i) i.base->value
#define plop(i) interval(new interval_base(i))
#define pltp base->value
#define plup u.base->value
#define plvp v.base->value

interval zero() {
  return plop(_interval_base());
}

bool is_empty(interval const &u) {
  assert(u.base);
  return empty(plup);
}

bool is_singleton(interval const &u) {
  assert(u.base);
  return singleton(plup);
}

bool contains_zero(interval const &u) {
  if (!u.base) return true;
  return in_zero(plup);
}

bool is_zero(interval const &u) {
  assert(u.base);
  return singleton(plup) && in_zero(plup);
}

interval hull(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(hull(plup, plvp));
}

interval intersect(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(intersect(plup, plvp));
}

std::pair< interval, interval > split(interval const &u) {
  assert(u.base);
  number m = median(plup);
  return std::make_pair(plop(_interval_base(plup.lower(), m)),
                        plop(_interval_base(m, plup.upper())));
}

bool interval::operator<=(interval const &v) const {
  if (!v.base) return true;
  if (!base) return false;
  return subset(pltp, plvp);
}

bool interval::operator<(interval const &v) const {
  if (!v.base) return true;
  if (!base) return false;
  return proper_subset(pltp, plvp);
}

interval operator-(interval const &u) {
  assert(u.base);
  return plop(-plup);
}

interval operator+(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(plup + plvp);
}

interval operator-(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(plup - plvp);
}

interval operator*(interval const &u, interval const &v) {
  assert(u.base && v.base);
  return plop(plup * plvp);
}

interval operator/(interval const &u, interval const &v) {
  assert(u.base && v.base && !contains_zero(v));
  return plop(plup / plvp);
}

interval square(interval const &u) {
  assert(u.base);
  return plop(square(plup));
}

interval from_exponent(int exp, int rnd) {
  number_base *l = new number_base, *u = new number_base;
  if (rnd == 0) {
    mpfr_set_ui_2exp(u->val, 1, exp, GMP_RNDN);
    mpfr_neg(l->val, u->val, GMP_RNDN);
  } else if (rnd < 0) {
    mpfr_set_si_2exp(l->val, -1, exp, GMP_RNDN);
    mpfr_set_ui(u->val, 0, GMP_RNDN);
  } else {
    mpfr_set_ui(l->val, 0, GMP_RNDN);
    mpfr_set_ui_2exp(u->val, 1, exp, GMP_RNDN);
  }
  return interval(number(l), number(u));
}

number const &lower(interval const &u) {
  assert(u.base);
  return plup.lower();
}

number const &upper(interval const &u) {
  assert(u.base);
  return plup.upper();
}

int sign(interval const &u) {
  assert(u.base);
  using namespace boost::numeric::interval_lib::user;
  return is_neg(plup.upper()) ? -1 : is_pos(plup.lower()) ? 1 : 0;
}

interval add_rev(interval const &u, interval const &r) {
  assert(u.base);
  if (!(r.base)) return interval();
  typedef real_policies::rounding rnd;
  number a = rnd::sub_down(lower(r), lower(u)), b = rnd::sub_up(upper(r), upper(u));
  if (!(a <= b)) return interval();
  return interval(a, b);
}

interval sub_rev(interval const &u, interval const &r) {
  assert(u.base);
  if (!(r.base)) return interval();
  typedef real_policies::rounding rnd;
  number a = rnd::sub_down(upper(u), upper(r)), b = rnd::sub_up(lower(u), lower(r));
  if (!(a <= b)) return interval();
  return interval(a, b);
}

interval square_rev(interval const &r) {
  if (!(r.base)) return interval();
  typedef real_policies::rounding rnd;
  number const &u = upper(r);
  if (boost::numeric::interval_lib::user::is_neg(u)) return interval();
  number a = rnd::sqrt_up(u);
  return interval(-a, a);
}
