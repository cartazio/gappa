#ifndef PROOFS_BASIC_PROOF_HPP
#define PROOFS_BASIC_PROOF_HPP

#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include "proofs/schemes.hpp"
#include <string>

struct rewrite_scheme: proof_scheme {
  ast_real const *rewritten;
  std::string name;
  ast_real_vect subs;
  rewrite_scheme(ast_real const *src, ast_real const *dst, std::string const &n, ast_real_vect const &s)
  	: proof_scheme(src), rewritten(dst), name(n), subs(s) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const { return ast_real_vect(1, rewritten); }
};

void register_user_rewrite(ast_real const *, ast_real const *);

#endif // PROOFS_BASIC_PROOF_HPP
