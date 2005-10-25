#include <algorithm>
#include <new>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/property.hpp"

typedef int long_is_not_long_enough[sizeof(long) - sizeof(interval *)];

property::property(): d(0), real() {}

property::property(ast_real const *r): real(r, PRED_BND) {
  new(&d) interval();
}

property::property(ast_real const *r, interval const &i): real(r, PRED_BND) {
  new(&d) interval(i);
}

property::property(predicated_real const &r, long i): d(i), real(r) {
  assert(r.pred() != PRED_BND);
}

property::property(property const &p): real(p.real) {
  if (p.real.pred() == PRED_BND) new(&d) interval(p.bnd());
  else d = p.d;
}

property::~property() {
  if (real.pred() == PRED_BND) bnd().~interval();
}

property &property::operator=(property const &p) {
  if (p.real.pred() == PRED_BND) {
    interval const &pb = p.bnd();
    if (real.pred() == PRED_BND) bnd() = pb;
    else new(&d) interval(pb);
  } else {
    if (real.pred() == PRED_BND) bnd().~interval();
    d = p.d;
  }
  real = p.real;
  return *this;
}

bool property::implies(property const &p) const {
  if (real != p.real) return false;
  switch (real.pred()) {
  case PRED_BND: return bnd() <= p.bnd();
  case PRED_FIX: return d >= p.d;
  case PRED_FLT: return d <= p.d;
  }
  assert(false);
  return false;
}

bool property::strict_implies(property const &p) const {
  if (real != p.real) return false;
  switch (real.pred()) {
  case PRED_BND: return bnd() < p.bnd();
  case PRED_FIX: return d > p.d;
  case PRED_FLT: return d < p.d;
  }
  assert(false);
  return false;
}

void property::intersect(property const &p) {
  assert(real == p.real);
  switch (real.pred()) {
  case PRED_BND: { interval &i = bnd(); i = ::intersect(i, p.bnd()); break; }
  case PRED_FIX: d = std::max(d, p.d); break;
  case PRED_FLT: d = std::min(d, p.d); break;
  }
}

typedef std::vector< property > vect;

bool property_vect::implies(property_vect const &s) const {
  for(const_iterator i = s.begin(), i_end = s.end(); i != i_end; ++i) {
    bool implies_i = false;
    for(const_iterator j = begin(), j_end = end(); j != j_end; ++j)
      if (j->implies(*i)) { implies_i = true; break; }
    if (!implies_i) return false;
  }
  return true;
}

int property_vect::find_compatible_property(property const &p) const {
  for(const_iterator i_begin = begin(), i = i_begin, i_end = end(); i != i_end; ++i)
    if (i->implies(p)) return i - i_begin;
  return -1;
}

void property_vect::push_front(property const &p) {
  vec.insert(vec.begin(), p);
}

void property_vect::replace_front(property const &p) {
  assert(vec.size() > 0);
  vec[0] = p;
}
