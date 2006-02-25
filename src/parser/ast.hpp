#ifndef PARSER_AST_HPP
#define PARSER_AST_HPP

#include <string>
#include <vector>
#include "parser/ast_real.hpp"

struct ast_atom_bound {
  ast_real const *real;
  ast_number const *lower, *upper;
  ast_atom_bound(ast_real const *r, ast_number const *l, ast_number const *u)
    : real(r), lower(l), upper(u) {}
};

enum ast_prop_type { PROP_ATOM, PROP_NOT, PROP_AND, PROP_OR, PROP_IMPL };

struct ast_prop {
  ast_prop_type type;
  ast_prop const *lhs, *rhs;
  ast_atom_bound const *atom;
  ast_prop(ast_atom_bound const *a): type(PROP_ATOM), atom(a) {}
  ast_prop(ast_prop const *p): type(PROP_NOT), lhs(p) {}
  ast_prop(ast_prop const *l, ast_prop_type t, ast_prop const *r): type(t), lhs(l), rhs(r) {}
};

typedef std::vector< ast_prop const * > ast_prop_vect;

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

enum ident_type { ID_NONE, ID_VAR, ID_FUN };

struct ast_ident {
  std::string name;
  ident_type type;
  union {
    function_generator const *fun;
    ast_real const *var;
  };
  ast_ident(std::string const &s): name(s), type(ID_NONE) {}
  bool operator<(ast_ident const &i) const { return name < i.name; }
  static ast_ident *find(std::string const &s);
  static ast_ident *temp();
};

std::string dump_real(ast_real const *, unsigned = 0);
struct property;
std::string dump_property(property const &);

inline ast_ident const *param_ident(unsigned long l) {
  return (l & 1) ? NULL : reinterpret_cast< ast_ident const * >(l);
}

inline bool param_int(unsigned long l, int &i) {
  i = static_cast< long >(l) >> 1;
  return (l & 1);
}

#endif // PARSER_AST_HPP
