#ifndef PROPERTY_HPP
#define PROPERTY_HPP

#include <vector>
#include "ast_real.hpp"
#include "numbers/interval.hpp"

struct property {
  ast_real const *real;
  interval bnd;
  property(): real(NULL) {}
  property(ast_real const *r): real(r) {}
  property(ast_real const *r, interval const &b): real(r), bnd(b) {}
  bool implies(property const &) const;
  bool operator<(property const &) const;
};

struct property_vect: std::vector< property > {
  bool implies(property_vect const &p) const;
  int find_compatible_property(property const &p) const;
};

#endif // PROPERTY_HPP
