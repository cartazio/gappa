#include "interval.hpp"
#include "interval_ext.hpp"
#include <cassert>

interval::interval(): desc(0), ptr(0) {}
interval::interval(interval_description const *d): desc(d), ptr(d ? (*d->create)() : 0) {}
interval::interval(interval_description const *d, void *p): desc(d), ptr(p) {}
interval::interval(interval const &v): desc(v.desc), ptr(v.desc ? (*v.desc->clone)(v.ptr) : 0) {}
interval::~interval() { if (desc) (*desc->destroy)(ptr); }

interval &interval::operator=(interval const &v) {
  if (this != &v) {
    if (desc) (*desc->destroy)(ptr);
    desc = v.desc;
    ptr = v.desc ? (*v.desc->clone)(v.ptr) : 0;
  }
  return *this;
}

bool is_singleton(interval const &v) {
  return (*v.desc->singleton)(v.ptr);
}

bool contains_zero(interval const &v) {
  if (!is_defined(v.desc)) return true;
  return (*v.desc->in_zero)(v.ptr);
}

bool is_zero(interval const &v) {
  return is_singleton(v) && contains_zero(v);
}

interval to_real(interval const &v) {
  return interval(interval_real, (*v.desc->to_real)(v.ptr));
}

interval hull(interval const &u, interval const &v) {
  assert(u.desc == v.desc);
  return interval(u.desc, (*u.desc->hull)(u.ptr, v.ptr));
}

interval intersect(interval const &u, interval const &v) {
  assert(u.desc == v.desc);
  return interval(u.desc, (*u.desc->intersect)(u.ptr, v.ptr));
}

std::pair< interval, interval > split(interval const &v) {
  std::pair< void *, void * > p = (*v.desc->split)(v.ptr);
  return std::make_pair(interval(v.desc, p.first), interval(v.desc, p.second));
}

std::ostream &operator<<(std::ostream &s, interval const &v) {
  (*v.desc->output)(s, v.ptr);
  return s;
}

interval operator+(interval const &u, interval const &v) {
  assert(u.desc == v.desc);
  return interval(u.desc, (*u.desc->add)(u.ptr, v.ptr));
}

interval operator-(interval const &u, interval const &v) {
  assert(u.desc == v.desc);
  return interval(u.desc, (*u.desc->sub)(u.ptr, v.ptr));
}

interval operator*(interval const &u, interval const &v) {
  assert(u.desc == v.desc);
  return interval(u.desc, (*u.desc->mul)(u.ptr, v.ptr));
}

interval operator/(interval const &u, interval const &v) {
  assert(u.desc == v.desc);
  return interval(u.desc, (*u.desc->div)(u.ptr, v.ptr));
}

bool operator<=(interval const &u, interval const &v) {
  if (!is_defined(v.desc)) return true;
  if (u.desc != v.desc) return false;
  return (*u.desc->subset)(u.ptr, v.ptr);
}
