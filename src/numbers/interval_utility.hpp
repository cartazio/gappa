#ifndef NUMBERS_INTERVAL_UTILITY_HPP
#define NUMBERS_INTERVAL_UTILITY_HPP

#include "interval.hpp"
#include <algorithm>
#include <iosfwd>

struct number_type;
struct number;

interval hull(interval const &, interval const &);
interval intersect(interval const &, interval const &);
interval from_exponent(int exp, int rnd);
std::pair< interval, interval > split(interval const &);
std::pair< interval, interval > split(interval const &, number_type const &);
number const &lower(interval const &);
number const &upper(interval const &);
std::ostream &operator<<(std::ostream &, number const &);
std::ostream &operator<<(std::ostream &, interval const &);

#endif // NUMBERS_INTERVAL_UTILITY_HPP
