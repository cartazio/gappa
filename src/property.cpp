#include "property.hpp"
#include "number.hpp"
#include "interval.hpp"

bool property_bound::operator>(property_bound const &p) const {
  return var == p.var && bnd <= p.bnd;
}

bool property_error::operator>(property_error const &p) const {
  return var == p.var && *real == *p.real && error == p.error && err <= p.err;
}

namespace {
struct do_imply: boost::static_visitor< bool > {
  template< class T >
  bool operator()(T const &v1, T const &v2) const { return v1 > v2; }
  template< class T, class U >
  typename boost::disable_if< boost::is_same< T, U >, bool >::type
  /*bool*/ operator()(T const &, U const &) const { return false; }
};
}

bool operator>(property const &v1, property const &v2) {
  return boost::apply_visitor(do_imply(), v1, v2);
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
