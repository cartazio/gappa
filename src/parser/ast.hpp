#ifndef PARSER_AST_HPP
#define PARSER_AST_HPP

#include "parser/ast_real.hpp"
#include <string>
#include <vector>

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

struct function;

enum ident_type { UNKNOWN_ID, REAL_FUN, REAL_VAR, REAL_RND };

struct ast_ident {
  std::string name;
  union {
    function const *fun;
    ast_real const *var;
    rounding_class const *rnd;
  };
  ident_type id_type;
  ast_ident(std::string const &s): name(s), id_type(UNKNOWN_ID) {}
  static ast_ident *find(std::string const &s);
  static ast_ident *temp();
};

struct function {
  real_op_type type;
  function(real_op_type t): type(t) {}
};

void clear_schemes();
std::string dump_real(ast_real const *, int = 0);

#endif // PARSER_AST_HPP
