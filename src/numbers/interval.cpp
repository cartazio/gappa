#include "interval.hpp"
#include "interval_ext.hpp"

static void destroyer(void *) {}
static void *cloner(void *) { return 0; }
static void *thrower() { throw; }
static void *thrower(void *) { throw; }
static void *thrower(void *, void *) { throw; }

interval_description interval_not_defined =
  { create: &thrower, destroy: &destroyer, clone: &cloner,
    add: &thrower, sub: &thrower, mul: &thrower, div: &thrower };

interval::interval(): desc(&interval_not_defined), ptr(0) {}
interval::interval(interval_description const *d): desc(d), ptr((*d->create)()) {}
interval::interval(interval_description const *d, void *p): desc(d), ptr(p) {}
interval::interval(interval const &v): desc(v.desc), ptr((*v.desc->clone)(v.ptr)) {}
interval::~interval() { (*desc->destroy)(ptr); }

interval &interval::operator=(interval const &v) {
  if (this != &v) {
    (*desc->destroy)(ptr);
    desc = v.desc;
    ptr = (*v.desc->clone)(v.ptr);
  }
  return *this;
}

interval operator+(interval const &u, interval const &v) {
  if (u.desc != v.desc) throw;
  return interval(u.desc, (*u.desc->add)(u.ptr, v.ptr));
}

interval operator-(interval const &u, interval const &v) {
  if (u.desc != v.desc) throw;
  return interval(u.desc, (*u.desc->sub)(u.ptr, v.ptr));
}

interval operator*(interval const &u, interval const &v) {
  if (u.desc != v.desc) throw;
  return interval(u.desc, (*u.desc->mul)(u.ptr, v.ptr));
}

interval operator/(interval const &u, interval const &v) {
  if (u.desc != v.desc) throw;
  return interval(u.desc, (*u.desc->div)(u.ptr, v.ptr));
}

bool is_defined(interval const &v) {
  return v.desc != &interval_not_defined;
}
