#ifndef NUMBERS_INTERVAL_EXT_HPP
#define NUMBERS_INTERVAL_EXT_HPP

#include "interval.hpp"
#include <algorithm>
#include <ostream>

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
  void *(*hull)(void *, void *);
  std::pair< void *, void * >(*split)(void *);
  void (*output)(std::ostream &, void *);
};

extern interval_description *interval_real;

inline bool is_defined(interval const &v) { return v.desc; }
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

std::ostream &operator<<(std::ostream &, interval const &);

#endif // NUMBERS_INTERVAL_EXT_HPP
