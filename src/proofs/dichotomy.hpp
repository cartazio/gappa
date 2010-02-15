#ifndef PROOFS_DICHOTOMY_HPP
#define PROOFS_DICHOTOMY_HPP

#include "parser/ast_real.hpp"

struct dichotomy_var {
  ast_real const *real;
  unsigned long splitter;
};

class number;

unsigned long fill_splitter(unsigned long, ast_number const *);
unsigned long fill_splitter(unsigned long, number const &);

typedef std::vector< dichotomy_var > dvar_vect;

struct dichotomy_hint {
  ast_real_vect dst;
  dvar_vect src;
};

typedef std::vector< dichotomy_hint > dichotomy_sequence;
extern dichotomy_sequence dichotomies;

#endif // PROOFS_DICHOTOMY_HPP
