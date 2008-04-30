#ifndef PROOFS_REWRITING_HPP
#define PROOFS_REWRITING_HPP

#include <string>
#include <vector>
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

typedef std::vector< pattern_cond > pattern_cond_vect;
typedef std::pair< ast_real const *, ast_real const * > pattern_excl;
typedef std::vector< pattern_excl > pattern_excl_vect;

struct rewriting_rule
{
  ast_real const *src, *dst;
  pattern_cond_vect cond;
  pattern_excl_vect excl;
  rewriting_rule(ast_real const *r1, ast_real const *r2, std::string const &n,
                 pattern_cond_vect const &c, pattern_excl_vect const &e);
};

typedef std::vector< rewriting_rule const * > rewriting_vect;
extern rewriting_vect rewriting_rules;

#endif // PROOFS_REWRITING_HPP
