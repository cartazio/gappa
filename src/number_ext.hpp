#ifndef NUMBER_EXT_HPP
#define NUMBER_EXT_HPP

#include "number.hpp"
#include "types.hpp"
#include <iostream>

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream,
   number_float32 const &value)
{
  float32_and_float f;
  f.soft = value.value;
  stream << f.hard;
  return stream;
}

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream,
   number_float64 const &value)
{
  float64_and_double f;
  f.soft = value.value;
  stream << f.hard;
  return stream;
}

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream,
   number_real const &value)
{
  mp_exp_t exp;
  char *buf = mpfr_get_str(NULL, &exp, 2, 5, value.data->val, GMP_RNDN);
  if (buf[0] == '-') stream << "-0." << buf + 1 << 'B' << exp;
  else stream << "0." << buf << 'B' << exp;
  free(buf);
  return stream;
}

struct ast_number;
impl_data *read_number(ast_number const &, type_id, mp_rnd_t);

number_real to_real(number_float32 const &);
number_real to_real(number_float64 const &);
number_real to_real(number_floatx80 const &);
number_real to_real(number_float128 const &);
int ulp_exponent(number_float32 const &);
int ulp_exponent(number_float64 const &);
int ulp_exponent(number_floatx80 const &);
int ulp_exponent(number_float128 const &);
int exponent(number_float32 const &);
int exponent(number_float64 const &);
int exponent(number_floatx80 const &);
int exponent(number_float128 const &);

#endif // NUMBER_EXT_HPP
