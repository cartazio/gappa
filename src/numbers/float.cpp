#include <boost/numeric/interval/interval.hpp>
#include <boost/numeric/interval/rounded_arith.hpp>
#include <boost/numeric/interval/checking.hpp>
#include <boost/numeric/interval/policies.hpp>
#include <boost/numeric/interval/arith.hpp>
#include <boost/numeric/interval/utility.hpp>
#include "interval_ext.hpp"
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

#define pcast(size,p) static_cast< interval_float##size * >(p)
#define cast(size,p) *static_cast< interval_float##size * >(p)

#define INTERVAL_FLOAT(size)		\
  typedef boost::numeric::interval< number_float##size > interval_float##size;	\
  static void *create_##size() { return new interval_float##size; }		\
  static void destroy_##size(void *v) { delete pcast(size,v); }			\
  static void *clone_##size(void *v) { return new interval_float##size(cast(size,v)); }	\
  static void *add_##size(void *u, void *v) { return new interval_float##size(cast(size,u) + cast(size,v)); }	\
  static void *sub_##size(void *u, void *v) { return new interval_float##size(cast(size,u) - cast(size,v)); }	\
  static void *mul_##size(void *u, void *v) { return new interval_float##size(cast(size,u) * cast(size,v)); }	\
  static void *div_##size(void *u, void *v) { return new interval_float##size(cast(size,u) / cast(size,v)); }	\
  static bool subset_##size(void *u, void *v) { return subset(cast(u), cast(v)); }	\
  static bool singleton_##size(void *v) { return singleton(cast(v)); }			\
  interval_description interval_float##size_desc =	\
    { create: &create_##size, destroy: &destroy_##size, clone: &clone_##size,	\
      add: &add_##size, sub: &sub_##size, mul: &mul_##size, div: &div_##size,	\
      subset: &subset_##size, singleton: singleton_##size };
