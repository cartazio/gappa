#ifndef NUMBERS_FLOAT_HPP
#define NUMBERS_FLOAT_HPP

#include <boost/numeric/interval/interval.hpp>
#include <boost/numeric/interval/rounded_arith.hpp>
#include <boost/numeric/interval/checking.hpp>
#include <boost/numeric/interval/policies.hpp>
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
  inline number_float##size sqrt(number_float##size const &v)	\
  { return number_float##size(float##size##_sqrt(v.value)); }	\
  extern interval_description *interval_float##size##_desc;		\
  typedef boost::numeric::interval< number_float##size > _interval_float##size;

NUMBER_FLOAT(32)
NUMBER_FLOAT(64)
NUMBER_FLOAT(x80)
NUMBER_FLOAT(128)

struct interval_float_description {
  interval_description desc;
  void *(*add)(void *, void *);
  void *(*sub)(void *, void *);
  void *(*mul)(void *, void *);
  void *(*div)(void *, void *);
  int (*mig_exp)(void *);
  int (*mag_exp)(void *);
  int prec;
  int min_exp;
  int format_size;
};

struct interval_float: interval {
  interval_float(interval_float_description const *, void *);
  interval_float(interval_float const &);
};

interval_float operator+(interval_float const &, interval_float const &);
interval_float operator-(interval_float const &, interval_float const &);
interval_float operator*(interval_float const &, interval_float const &);
interval_float operator/(interval_float const &, interval_float const &);

#endif // NUMBERS_FLOAT_HPP
