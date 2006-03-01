#ifndef NUMBERS_INTERVAL_UTILITY_HPP
#define NUMBERS_INTERVAL_UTILITY_HPP

#include <algorithm>
#include <iosfwd>
#include "interval.hpp"

struct number;

interval hull(interval const &, interval const &);
interval intersect(interval const &, interval const &);
interval from_exponent(int exp, int rnd);
std::pair< interval, interval > split(interval const &);
std::pair< interval, interval > split(interval const &, double);
number const &lower(interval const &);
number const &upper(interval const &);
std::ostream &operator<<(std::ostream &, number const &);
std::ostream &operator<<(std::ostream &, interval const &);
int sign(interval const &);

#endif // NUMBERS_INTERVAL_UTILITY_HPP
