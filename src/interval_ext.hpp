#ifndef INTERVAL_EXT_HPP
#define INTERVAL_EXT_HPP

#include "interval.hpp"
#include <iostream>

interval to_real(interval const &);
int ulp_exponent(interval const &);
interval from_exponent(int, mp_rnd_t);
int mig_exponent(interval const &);
int mag_exponent(interval const &);
bool is_singleton(interval const &);
bool is_not_defined(interval const &);

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream,
   interval const &value);

#endif // INTERVAL_EXT_HPP
