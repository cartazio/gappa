#include <boost/numeric/interval/interval.hpp>
#include <boost/numeric/interval/rounded_arith.hpp>
#include <boost/numeric/interval/checking.hpp>
#include <boost/numeric/interval/policies.hpp>
#include "interval.hpp"
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
