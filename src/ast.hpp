#ifndef AST_HPP
#define AST_HPP

#include <string>
#include <vector>
#include "ast_real.hpp"
#include "property.hpp"
#include "program.hpp"

struct ast_interval {
  ast_number const *lower, *upper;
};

struct ast_atom_bound {
  ast_real const *real;
  ast_interval interval;
  ast_atom_bound(ast_real const *r, ast_interval i): real(r), interval(i) {}
};

struct ast_prop_and;
struct ast_prop_impl;

typedef boost::variant
  < boost::recursive_wrapper< ast_prop_and >
  , boost::recursive_wrapper< ast_prop_impl >
  , ast_atom_bound
  > ast_prop;

struct ast_prop_and: std::vector< ast_prop > {};

struct ast_prop_impl {
  ast_prop left, right;
};

void clear_schemes();

#endif // AST_HPP
