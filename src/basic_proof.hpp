#ifndef BASIC_PROOF_HPP
#define BASIC_PROOF_HPP

#include "property.hpp"
#include "proof_graph.hpp"
#include <string>

extern node *triviality;

struct proof_scheme
{
  virtual node *generate_proof(property_vect const &, property &) const = 0;
  virtual ast_real_vect needed_reals(ast_real const *) const = 0;
  virtual ~proof_scheme() {}
  proof_scheme(): next(NULL) {}
  proof_scheme const *next;
};

struct instruction;

struct node_theorem: node {
  std::string name;
  node_theorem(int nb, property const *h, property const &p, std::string n);
};

node *handle_proof(property_vect const &, property &);
bool generate_scheme_tree(property_vect const &hyp, ast_real const *);

#endif // BASIC_PROOF_HPP
