#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/property.hpp"

bool property::implies(property const &p) const {
  return real == p.real && bnd <= p.bnd;
}

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
  for(int i = 0, l = size(); i < l; ++i)
    if ((*this)[i].implies(p)) return i;
  return -1;
}

bool property_vect::operator==(property_vect const &v) const {
  unsigned l = size();
  if (l != v.size()) return false;
  for(unsigned i = 0; i < l; ++i) {
    property const &p1 = (*this)[i], &p2 = v[i];
    if (p1.real != p2.real || lower(p1.bnd) != lower(p2.bnd) || upper(p1.bnd) != upper(p2.bnd))
      return false;
  }
  return true;
}
