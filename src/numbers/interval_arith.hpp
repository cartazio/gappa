#ifndef NUMBERS_INTERVAL_ARITH_HPP
#define NUMBERS_INTERVAL_ARITH_HPP

#include "interval.hpp"

interval operator+(interval const &, interval const &);
interval operator-(interval const &, interval const &);
interval operator*(interval const &, interval const &);
interval operator/(interval const &, interval const &);
interval operator-(interval const &);

#endif // NUMBERS_INTERVAL_ARITH_HPP
