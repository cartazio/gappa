#ifndef NUMBERS_INTERVAL_EXT_HPP
#define NUMBERS_INTERVAL_EXT_HPP

#include "interval.hpp"
#include <algorithm>

struct interval_description {
  void *(*create)();
  void (*destroy)(void *);
  void *(*clone)(void *);
  void *(*add)(void *, void *);
  void *(*sub)(void *, void *);
  void *(*mul)(void *, void *);
  void *(*div)(void *, void *);
  bool (*subset)(void *, void *);
  bool (*singleton)(void *);
  bool (*in_zero)(void *);
  void *(*to_real)(void *);
};

extern interval_description interval_not_defined;
extern interval_description interval_real_desc;

bool is_defined(interval const &);
bool is_singleton(interval const &);
bool is_zero(interval const &);
bool contains_zero(interval const &);

interval to_real(interval const &);
interval hull(interval const &, interval const &);

std::pair< interval, interval > split(interval const &);

interval operator+(interval const &, interval const &);
interval operator-(interval const &, interval const &);
interval operator*(interval const &, interval const &);
interval operator/(interval const &, interval const &);
bool operator<=(interval const &, interval const &);

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &s,
   interval const &) { return s; }

#endif // NUMBERS_INTERVAL_EXT_HPP
