#ifndef PROPERTY_HPP
#define PROPERTY_HPP

#include <vector>
#include "ast_real.hpp"
#include "interval.hpp"

struct variable;

struct property_bound;
struct property_error;

typedef boost::variant
  < property_bound,
    property_error > property;

bool operator>(property const &, property const &);

struct property_bound {
  variable *var;
  interval bnd;
  bool operator>(property_bound const &p) const;
};

struct property_error {
  variable *var;
  ast_real const *real;
  interval err;
  int error;
  bool operator>(property_error const &p) const;
};

struct property_vect: std::vector< property > {
  bool operator>(property_vect const &p) const;
  int find_compatible_property(property const &p) const;
};

#endif // PROPERTY_HPP
