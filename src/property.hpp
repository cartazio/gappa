#ifndef PROPERTY_HPP
#define PROPERTY_HPP

#include <vector>
#include "ast_real.hpp"
#include "numbers/interval.hpp"

struct variable;

enum property_type { PROP_BND, PROP_ABS, PROP_REL };

struct property {
  property_type type;
  variable *var; // only used for ABS and REL
  interval bnd;
  ast_real const *real;
  property(): type(property_type(-1)) {}
  property(property_type t): type(t) {}
  bool implies(property const &) const;
  bool operator<(property const &) const;
};

struct property_vect: std::vector< property > {
  bool implies(property_vect const &p) const;
  int find_compatible_property(property const &p) const;
};

#endif // PROPERTY_HPP
