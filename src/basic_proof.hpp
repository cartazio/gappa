#ifndef BASIC_PROOF_HPP
#define BASIC_PROOF_HPP

#include "property.hpp"

struct node;

struct generator {
  property res;
  virtual node *do_it() = 0;
  generator(property const &p): res(p) {}
  virtual ~generator() {}
};

generator *generate_basic_proof(property_vect const &, property const &);

#endif // BASIC_PROOF_HPP
