#ifndef INTERVAL_HPP
#define INTERVAL_HPP

#include "number.hpp"
#include "types.hpp"
#include <boost/variant.hpp>
#include <boost/numeric/interval/interval.hpp>
#include <boost/numeric/interval/rounded_arith.hpp>
#include <boost/numeric/interval/checking.hpp>
#include <boost/numeric/interval/policies.hpp>

namespace _bn = boost::numeric;

namespace {

class real_policies {
  typedef number_real T;
public:
# define RES(name) impl_data *name = new impl_data()
  struct rounding {
    static T conv_down(int v)		{ RES(w); mpfr_set_si(w->val, v, GMP_RNDD); return T(w); }
    static T conv_up  (int v)		{ RES(w); mpfr_set_si(w->val, v, GMP_RNDU); return T(w); }
  /*static T conv_down(double v)	{ RES(w); mpfr_set_d(w->val, v, GMP_RNDD); return T(w); }
    static T conv_up  (double v)	{ RES(w); mpfr_set_d(w->val, v, GMP_RNDU); return T(w); }*/
    static T conv_down(T const &v)	{ return v; }
    static T conv_up  (T const &v)	{ return v; }
    static T opp_down(T const &v)	{ RES(w); mpfr_neg(w->val, v.data->val, GMP_RNDD); return T(w); }
    static T opp_up  (T const &v)	{ RES(w); mpfr_neg(w->val, v.data->val, GMP_RNDU); return T(w); }
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
    typedef rounding unprotected_rounding;
  };
  struct checking {
    static bool is_nan(int) { return false; }
    static bool is_nan(double v) { return (v != v); }
    static bool is_nan(T const &v) { return mpfr_nan_p(v.data->val); }
    static T empty_lower() { return T(); }
    static T empty_upper() { return T(); }
    static T pos_inf() { RES(w); mpfr_set_inf(w->val, +1); return T(w); }
    static T neg_inf() { RES(w); mpfr_set_inf(w->val, -1); return T(w); }
    static bool is_empty(T const &x, T const &y) { return !(x <= y); }
  };
# undef RES
};

}

typedef _bn::interval< number_float32 > interval_float32;
typedef _bn::interval< number_float64 > interval_float64;
typedef _bn::interval< number_floatx80 > interval_floatx80;
typedef _bn::interval< number_float128 > interval_float128;
typedef _bn::interval< number_real, real_policies > interval_real;

struct interval_not_defined {};

typedef boost::variant
  < interval_not_defined
  , interval_float32
  , interval_float64
  , interval_floatx80
  , interval_float128
  , interval_real
  > interval_variant;

struct ast_interval;

struct interval {
  interval_variant value;
  interval() {}
  interval(interval_variant const &v): value(v) {}
  interval(ast_interval const &, bool widen, type_id = UNDEFINED);
  interval operator+(interval const &) const;
  interval operator-(interval const &) const;
  interval operator*(interval const &) const;
  interval operator/(interval const &) const;
  bool operator<=(interval const &) const;
};

#endif // INTERVAL_HPP
