#include "program.hpp"
#include "property.hpp"
#include "numbers/interval_ext.hpp"

bool property::implies(property const &p) const {
  if (type != p.type || real != p.real) return false;
  if (type != PROP_BND && var != p.var) return false;
  return bnd <= p.bnd;
}

bool property_vect::implies(property_vect const &s) const {
  bool implies_all = true;
  for(const_iterator i = s.begin(), i_end = s.end(); i != i_end; ++i) {
    if (i->type != PROP_BND && i->var->real == i->real) {
      assert(contains_zero(i->bnd));
      continue; // tautology
    }
    bool implies_i = false;
    for(const_iterator j = begin(), j_end = end(); j != j_end; ++j)
      if (j->implies(*i)) { implies_i = true; break; }
    if (!implies_i) { implies_all = false; break; }
  }
  return implies_all;
}

int property_vect::find_compatible_property(property const &p) const {
  for(int i = 0, l = size(); i < l; ++i)
    if ((*this)[i].implies(p)) return i;
  return -1;
}
