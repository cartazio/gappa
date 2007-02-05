#ifndef NUMBERS_INTERVAL_ARITH_HPP
#define NUMBERS_INTERVAL_ARITH_HPP

#include "interval.hpp"

interval operator+(interval const &, interval const &);
interval operator-(interval const &, interval const &);
interval operator*(interval const &, interval const &);
interval operator/(interval const &, interval const &);
interval operator-(interval const &);
interval abs(interval const &);
interval square(interval const &);
interval sqrt(interval const &);
interval compose_relative(interval const &, interval const &);
interval add_relative(interval const &, interval const &, interval const &);

#endif // NUMBERS_INTERVAL_ARITH_HPP
