#include "property.hpp"
#include "number.hpp"
#include "interval.hpp"

bool operator>(property const &u, property const &v) {
  if (u.type != v.type || u.var != v.var) return false;
  if (u.type != PROP_BND && !(*u.real == *v.real)) return false;
  return u.bnd <= v.bnd;
}

bool property_vect::operator>(property_vect const &s) const {
  bool a = true;
  for(const_iterator i = s.begin(); i != s.end(); ++i) {
    bool b = false;
    for(const_iterator j = begin(); j != end(); ++j)
      if (*j > *i) { b = true; break; }
    if (!b) { a = false; break; }
  }
  return !a;
}

int property_vect::find_compatible_property(property const &p) const {
  int l = size();
  for(int i = 0; i < l; i++) if ((*this)[i] > p) return i;
  return -1;
}
