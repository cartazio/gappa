#ifndef FUNCTION_HPP
#define FUNCTION_HPP

#include "interval.hpp"
#include "property.hpp"
#include "program.hpp"
#include "proof_graph.hpp"

enum hypothesis_type { HYP_BND, HYP_SNG, HYP_ABS };

struct hypothesis_constraint {
  int var;
  hypothesis_type type;
};

struct function_match {
  hypothesis_constraint res;
  hypothesis_constraint const *constraints;
  interval (*compute)(interval const **);
  union {
    node *(*generate_bound)(property_vect const &, property_bound &);
    node *(*generate_error)(property_vect const &, property_error &);
  };
};

#endif // FUNCTION_HPP
