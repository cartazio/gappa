#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/property.hpp"
#include <algorithm>

bool property::implies(property const &p) const {
  return real == p.real && bnd <= p.bnd;
}

typedef std::vector< property > vect;
typedef std::vector< vect > hypotheses;
static hypotheses store;

static bool operator==(vect const &v1, vect const &v2) {
  unsigned l = v1.size();
  if (v1.size() != v2.size()) return false;
  for(unsigned i = 0; i < l; ++i) {
    property const &p1 = v1[i], &p2 = v2[i];
    if (p1.real != p2.real || lower(p1.bnd) != lower(p2.bnd) || upper(p1.bnd) != upper(p2.bnd))
      return false;
  }
  return true;
}

property_vect::vect const &property_vect::get() const {
  if (well_known < 0) return vec;
  return store[well_known];
}

property_vect::const_iterator property_vect::begin() const {
  return get().begin();
}

property_vect::const_iterator property_vect::end() const {
  return get().end();
}

void property_vect::publish() {
  hypotheses::const_iterator
    begin = store.begin(),
    end = store.end(),
    i = std::find(begin, end, vec);
  if (i == end) {
    well_known = store.size();
    store.push_back(vec);
  } else well_known = i - begin;
  vec.clear();
}

bool property_vect::implies(property_vect const &s) const {
  if (well_known >= 0 && well_known == s.well_known) return true;
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

bool property_vect::operator==(property_vect const &v) const {
  if (well_known >= 0) return well_known == v.well_known;
  return get() == v.get();
}

property const &property_vect::operator[](unsigned i) const {
  return get()[i];
}

unsigned property_vect::size() const {
  return get().size();
}

void property_vect::push_front(property const &p) {
  if (well_known >= 0) { vec = store[well_known]; well_known = -1; }
  vec.insert(vec.begin(), p);
}

void property_vect::push_back(property const &p) {
  if (well_known >= 0) { vec = store[well_known]; well_known = -1; }
  vec.push_back(p);
}

void property_vect::replace_front(property const &p) {
  if (well_known >= 0) { vec = store[well_known]; well_known = -1; }
  assert(vec.size() > 0);
  vec[0] = p;
}
