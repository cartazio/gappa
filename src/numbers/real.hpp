#ifndef NUMBERS_REAL_HPP
#define NUMBERS_REAL_HPP

#include <gmp.h>
#include <mpfr.h>
#include "interval_ext.hpp"

struct ref_counter_t {
  int nb;
  ref_counter_t(): nb(1) {}
  void incr() { ++nb; }
  bool decr() { return --nb == 0; }
};

namespace {
int const real_prec = 128;

struct impl_data {
  mutable ref_counter_t ref_counter;
  mpfr_t val;
  impl_data() { mpfr_init2(val, real_prec); }
  ~impl_data() { mpfr_clear(val); }
  impl_data const *clone() const { ref_counter.incr(); return this; }
  impl_data *unique() const;
  void destroy() const { if (ref_counter.decr()) delete this; }
};

impl_data *empty_mpfr = new impl_data();
} // anonymous namespace

struct number_real {
  impl_data const *data;
  mpfr_t const &mpfr_data() const { return data->val; }

  number_real(): data(empty_mpfr->clone()) {}
  number_real(int v);
  number_real(impl_data const *d): data(d) {}
  number_real(number_real const &v): data(v.data->clone()) {}
  number_real &operator=(number_real const &v) {
    impl_data const *d = v.data->clone();
    data->destroy();
    data = d;
    return *this;
  }
  ~number_real() { data->destroy(); }
  bool operator<=(number_real const &v) const;
  bool operator==(number_real const &v) const;
  number_real operator-() const {
    impl_data *r = new impl_data();
    mpfr_neg(r->val, data->val, GMP_RNDN);
    return number_real(r);
  }
};

number_real const &min(number_real const &x, number_real const &y);
number_real const &max(number_real const &x, number_real const &y);

namespace boost { namespace numeric { namespace interval_lib { namespace user {

inline bool is_zero(::number_real const &v) { return mpfr_sgn(v.data->val) == 0; }
inline bool is_neg(::number_real const &v)  { return mpfr_sgn(v.data->val) < 0; }
inline bool is_pos(::number_real const &v)  { return mpfr_sgn(v.data->val) > 0; }

} } } }

#include <boost/numeric/interval/interval.hpp>
#include <boost/numeric/interval/rounded_arith.hpp>
#include <boost/numeric/interval/checking.hpp>
#include <boost/numeric/interval/policies.hpp>
#include <boost/numeric/interval/arith.hpp>
#include <boost/numeric/interval/utility.hpp>

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

typedef boost::numeric::interval< number_real, real_policies > _interval_real;

#endif // NUMBER_REAL_HPP
