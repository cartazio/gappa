#ifndef PROOFS_REWRITING_HPP
#define PROOFS_REWRITING_HPP

#include <string>
#include <vector>
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

struct rewriting_factory;
typedef std::vector< pattern_cond > pattern_cond_vect;
typedef std::pair< ast_real const *, ast_real const * > pattern_excl;
typedef std::vector< pattern_excl > pattern_excl_vect;
typedef std::vector< rewriting_factory const * > rewriting_vect;

extern rewriting_vect rewriting_rules;

struct rewriting_factory: scheme_factory {
  ast_real const *dst;
  std::string name;
  pattern_cond_vect cond;
  pattern_excl_vect excl;
  virtual proof_scheme *operator()(predicated_real const &, ast_real_vect const &) const;
  rewriting_factory(ast_real const *p1, ast_real const *p2, std::string const &n,
                    pattern_cond_vect const &c, pattern_excl_vect const &e);
};

#endif // PROOFS_REWRITING_HPP
