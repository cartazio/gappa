#ifndef PROPERTY_HPP
#define PROPERTY_HPP

#include <vector>
#include "ast_real.hpp"
#include "interval.hpp"

struct variable;

enum property_type { PROP_BND, PROP_ABS, PROP_REL };

struct property {
  property_type type;
  variable *var;
  interval bnd;
  ast_real const *real; // only used for ABS and REL
  property(): type(property_type(-1)) {}
  property(property_type t): type(t) {}
};

bool operator>(property const &, property const &);

struct property_vect: std::vector< property > {
  bool operator>(property_vect const &p) const;
  int find_compatible_property(property const &p) const;
};

#endif // PROPERTY_HPP
