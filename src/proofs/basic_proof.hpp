#ifndef PROOFS_BASIC_PROOF_HPP
#define PROOFS_BASIC_PROOF_HPP

#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include <string>

extern node *triviality;

struct node_theorem: node {
  std::string name;
  node_theorem(int nb, property const *h, property const &p, std::string n);
};

node *generate_triviality(property_vect const &hyp, property &res);

#endif // PROOFS_BASIC_PROOF_HPP
