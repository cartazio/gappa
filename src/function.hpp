#ifndef FUNCTION_HPP
#define FUNCTION_HPP

#include "interval.hpp"
#include "property.hpp"
#include "program.hpp"
#include "proof_graph.hpp"

enum hypothesis_type { HYP_BND, HYP_SNG, HYP_ABS, HYP_REL };

struct hypothesis_constraint {
  int var;
  hypothesis_type type;
};

struct bound_computation {
  interval (*compute)(interval const **);
  node *(*generate)(property_bound const *, property_bound &);
};

struct error_computation {
  hypothesis_constraint res;
  hypothesis_constraint const *constraints;
  interval (*compute)(interval const **);
  node *(*generate)(property_vect const &, property_error &);
};

#endif // FUNCTION_HPP
