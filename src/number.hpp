#ifndef NUMBER_HPP
#define NUMBER_HPP

#include <gmp.h>
#include <mpfr.h>
#include <cassert>
#include <ostream>
extern "C" {
#include "softfloat.h"
}

#define NUMBER_FLOAT(size)			\
  struct number_float##size {			\
    typedef number_float##size type;		\
    float##size value;				\
    number_float##size(int v): value(int32_to_float##size(v)) {}	\
    number_float##size(float##size v): value(v) {}			\
    type operator-() const { return type(float##size##_neg(value)); }	\
    type operator+(type const &v) const { return type(float##size##_add(value, v.value)); }	\
    type operator-(type const &v) const { return type(float##size##_sub(value, v.value)); }	\
    type operator*(type const &v) const { return type(float##size##_mul(value, v.value)); }	\
    type operator/(type const &v) const { return type(float##size##_div(value, v.value)); }	\
    bool operator!=(type const &v) const { return !float##size##_eq(value, v.value); }	\
    bool operator==(type const &v) const { return float##size##_eq(value, v.value); }	\
    bool operator<=(type const &v) const { return float##size##_le(value, v.value); }	\
    bool operator>=(type const &v) const { return !float##size##_lt(value, v.value); }	\
    bool operator<(type const &v) const { return float##size##_lt(value, v.value); }	\
    bool operator>(type const &v) const { return !float##size##_le(value, v.value); }	\
  }; \
  inline number_float##size sqrt(number_float##size const &v) { return number_float##size(float##size##_sqrt(v.value)); }

NUMBER_FLOAT(32)
NUMBER_FLOAT(64)
NUMBER_FLOAT(x80)
NUMBER_FLOAT(128)

union float32_and_float {
  float32 soft;
  float hard;
};

union float64_and_double {
  float64 soft;
  double hard;
};

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
}

struct number_real {
  impl_data const *data;
  mpfr_t const &mpfr_data() const { return data->val; }

  number_real() { data = empty_mpfr->clone(); }
  number_real(int v);
  number_real(impl_data const *d) { data = d; }
  number_real(number_real const &v) { data = v.data->clone(); }
  number_real &operator=(number_real const &v) { impl_data const *d = v.data->clone(); data->destroy(); data = d; return *this; }
  ~number_real() { data->destroy(); }
  bool operator<=(number_real const &v) const;
  bool operator==(number_real const &v) const;
};

number_real const &min(number_real const &x, number_real const &y);
number_real const &max(number_real const &x, number_real const &y);

namespace boost { namespace numeric { namespace interval_lib { namespace user {

inline bool is_zero(::number_real const &v) { return mpfr_sgn(v.data->val) == 0; }
inline bool is_neg(::number_real const &v)  { return mpfr_sgn(v.data->val) < 0; }
inline bool is_pos(::number_real const &v)  { return mpfr_sgn(v.data->val) > 0; }

} } } }

#endif // NUMBER_HPP
