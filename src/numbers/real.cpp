#include "real.hpp"

#define pcast(p) static_cast< interval_real * >(p)
#define cast(p) *static_cast< interval_real * >(p)

static void *create() { return new interval_real; }
static void destroy(void *v) { delete pcast(v); }
static void *clone(void *v) { return new interval_real(cast(v)); }
static void *add(void *u, void *v) { return new interval_real(cast(u) + cast(v)); }
static void *sub(void *u, void *v) { return new interval_real(cast(u) - cast(v)); }
static void *mul(void *u, void *v) { return new interval_real(cast(u) * cast(v)); }
static void *div(void *u, void *v) { return new interval_real(cast(u) / cast(v)); }
static bool subset(void *u, void *v) { return subset(cast(u), cast(v)); }
static bool singleton(void *v) { return singleton(cast(v)); }

interval_description interval_real_desc =
  { create: &create, destroy: &destroy, clone: &clone,
    add: &add, sub: &sub, mul: &mul, div: &div,
    subset: &subset, singleton: &singleton };
