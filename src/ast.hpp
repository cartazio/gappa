#ifndef AST_HPP
#define AST_HPP

#include <string>
#include <vector>
#include "ast_real.hpp"
#include "property.hpp"
#include "program.hpp"

struct ast_interval {
  ast_number lower, upper;
  ast_interval(ast_number const &l, ast_number const &u): lower(l), upper(u) {}
};

struct ast_operands {
  std::vector< ast_ident * > ops;
};

struct ast_atom_bound {
  variable *ident;
  ast_interval *interval;
  ast_atom_bound(variable *v, ast_interval *i): ident(v), interval(i) {}
};

struct ast_atom_error {
  variable *ident;
  ast_real *real;
  ast_interval *interval;
  int error;
  ast_atom_error(int e, variable *v, ast_real *r, ast_interval *i):
    ident(v), real(r), interval(i), error(e) {}
};

struct ast_atom_approx {
  variable *ident;
  ast_number value;
  ast_atom_approx(variable *i, ast_number const &v): ident(i), value(v) {}
};

struct ast_prop_and;
struct ast_prop_impl;

typedef boost::variant
  < boost::recursive_wrapper< ast_prop_and >
  , boost::recursive_wrapper< ast_prop_impl >
  , ast_atom_bound
  , ast_atom_error
  , ast_atom_approx
  > ast_prop;

struct ast_prop_and: std::vector< ast_prop > {};

struct ast_prop_impl {
  ast_prop left, right;
};

void make_variables_real();

#endif // AST_HPP
