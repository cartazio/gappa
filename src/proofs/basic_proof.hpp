#ifndef PROOFS_BASIC_PROOF_HPP
#define PROOFS_BASIC_PROOF_HPP

#include <string>
#include "parser/pattern.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include "proofs/schemes.hpp"

struct rewrite_scheme: proof_scheme {
  ast_real const *rewritten;
  std::string name;
  pattern_cond_vect conditions;
  rewrite_scheme(ast_real const *src, ast_real const *dst, std::string const &n)
  	: proof_scheme(src), rewritten(dst), name(n) {}
  rewrite_scheme(ast_real const *src, ast_real const *dst, std::string const &n, pattern_cond_vect const &c)
  	: proof_scheme(src), rewritten(dst), name(n), conditions(c) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
};

void register_user_rewrite(ast_real const *, ast_real const *);

#endif // PROOFS_BASIC_PROOF_HPP
