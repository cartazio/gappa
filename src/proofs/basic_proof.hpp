#ifndef PROOFS_BASIC_PROOF_HPP
#define PROOFS_BASIC_PROOF_HPP

#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include "proofs/schemes.hpp"
#include <string>

extern node *triviality;

struct node_theorem: node {
  std::string name;
  node_theorem(int nb, property const *h, property const &p, std::string n);
};

node *generate_triviality(property_vect const &hyp, property &res);

struct rewrite_scheme: proof_scheme {
  ast_real const *real;
  std::string name;
  rewrite_scheme(ast_real const *r, std::string const &n): real(r), name(n) {}
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(1, real); }
};

#endif // PROOFS_BASIC_PROOF_HPP
