#ifndef PROOFS_BASIC_PROOF_HPP
#define PROOFS_BASIC_PROOF_HPP

#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include "proofs/schemes.hpp"
#include <string>

struct rewrite_scheme: proof_scheme {
  ast_real const *real;
  std::string name;
  rewrite_scheme(ast_real const *r, std::string const &n): real(r), name(n) {}
  virtual node *generate_proof(ast_real const *) const;
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(1, real); }
};

void register_user_rewrite(ast_real const *, ast_real const *);

#endif // PROOFS_BASIC_PROOF_HPP
