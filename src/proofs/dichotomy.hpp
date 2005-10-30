#ifndef PROOFS_DICHOTOMY_HPP
#define PROOFS_DICHOTOMY_HPP

#include "parser/ast_real.hpp"

struct dichotomy_hint {
  ast_real_vect src, dst;
};

typedef std::vector< dichotomy_hint > dichotomy_sequence;
extern dichotomy_sequence dichotomies;

#endif // PROOFS_DICHOTOMY_HPP
