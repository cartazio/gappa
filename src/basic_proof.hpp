#ifndef BASIC_PROOF_HPP
#define BASIC_PROOF_HPP

#include "property.hpp"
#include "proof_graph.hpp"
#include <string>

extern node *triviality;

struct proof_scheme
{
  node *(*generate_proof)(property_vect const &, property &);
  proof_scheme const *next;
};

struct instruction;

struct node_theorem: node {
  std::string name;
  node_theorem(int nb, property const *h, property const &p, std::string n);
};

void add_scheme(ast_real const *, node *(*)(property_vect const &, property &));
void add_basic_scheme(ast_real *);
node *handle_proof(property_vect const &, property &);

#endif // BASIC_PROOF_HPP
