#ifndef NUMBERS_TYPES_HPP
#define NUMBERS_TYPES_HPP

struct float_format;
struct number;

struct number_type {
  float_format const *format;
  number rounded_up(number const &) const;
  number rounded_dn(number const &) const;
};

extern number_type real_type;

namespace {
const number_type *REAL_NUMBER = &real_type;
const number_type *UNDEFINED = 0;
}

#endif // NUMBERS_TYPES_HPP
