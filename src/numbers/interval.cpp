#include "interval.hpp"
#include "interval_ext.hpp"

static void destroyer(void *) {}
static void *cloner(void *) { return 0; }
static void *thrower_p() { throw; }
//static void *thrower_p(void *) { throw; }
static void *thrower_p(void *, void *) { throw; }
static bool thrower_b(void *, void *) { throw; }

interval_description interval_not_defined =
  { create: &thrower_p, destroy: &destroyer, clone: &cloner,
    add: &thrower_p, sub: &thrower_p, mul: &thrower_p, div: &thrower_p,
    subset: &thrower_b };

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

bool is_defined(interval const &v) {
  return v.desc != &interval_not_defined;
}

bool is_singleton(interval const &v) {
  return (*v.desc->singleton)(v.ptr);
}

//bool contains_zero(interval const &v);

bool is_zero(interval const &v) {
  return is_singleton(v) && contains_zero(v);
}

interval to_real(interval const &v) {
  return interval(&interval_real_desc, (*v.desc->to_real)(v.ptr));
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

bool operator<=(interval const &u, interval const &v) {
  if (v.desc == &interval_not_defined) return true;
  if (u.desc != v.desc) return false;
  return (*u.desc->subset)(u.ptr, v.ptr);
}
