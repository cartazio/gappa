#ifndef PROOFS_DICHOTOMY_HPP
#define PROOFS_DICHOTOMY_HPP

#include "proofs/schemes.hpp"

struct dichotomy_scheme: proof_scheme {
  ast_real const *real;
  dichotomy_scheme(ast_real const *r): real(r) {}
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
};

void register_user_dichotomy(ast_real const *, ast_real const *);

#endif // PROOFS_DICHOTOMY_HPP
