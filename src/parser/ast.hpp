#ifndef PARSER_AST_HPP
#define PARSER_AST_HPP

#include <string>
#include <vector>
#include "parser/ast_real.hpp"

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

typedef std::vector< unsigned long > function_params;

struct function_generator {
  function_generator(bool) {}
  function_generator(const char *);
  virtual function_class const *operator()(function_params const &) const = 0;
  virtual ~function_generator() {}
};

struct default_function_generator: function_generator {
  function_class const *fun;
  default_function_generator(function_class const *f): function_generator(false), fun(f) {}
  default_function_generator(const char *s, function_class const *f): function_generator(s), fun(f) {}
  virtual function_class const *operator()(function_params const &) const;
};

struct ast_ident {
  std::string name;
  function_generator const *fun;
  ast_real const *var;
  ast_ident(std::string const &s): name(s), fun(NULL), var(NULL) {}
  bool operator<(ast_ident const &i) const { return name < i.name; }
  static ast_ident *find(std::string const &s);
  static ast_ident *temp();
};

std::string dump_real(ast_real const *, unsigned = 0);

inline ast_ident const *param_ident(unsigned long l) {
  return (l & 1) ? NULL : reinterpret_cast< ast_ident const * >(l);
}

inline bool param_int(unsigned long l, int &i) {
  i = static_cast< long >(l) >> 1;
  return (l & 1);
}

#endif // PARSER_AST_HPP
