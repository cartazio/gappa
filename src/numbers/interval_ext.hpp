#ifndef NUMBERS_INTERVAL_EXT_HPP
#define NUMBERS_INTERVAL_EXT_HPP

#include "interval.hpp"

struct interval_description {
  void *(*create)();
  void (*destroy)(void *);
  void *(*clone)(void *);
  void *(*add)(void *, void *);
  void *(*sub)(void *, void *);
  void *(*mul)(void *, void *);
  void *(*div)(void *, void *);
};

extern interval_description interval_not_defined;
bool is_defined(interval const&);

#endif // NUMBERS_INTERVAL_EXT_HPP
