#ifndef PROGRAM_HPP
#define PROGRAM_HPP

#include <vector>
#include <iostream>
#include "types.hpp"

struct ast_ident;
struct instruction;

struct variable {
  ast_ident *name;
  type_id type;
  variable(ast_ident *n, type_id t = UNDEFINED): name(n), type(t), def(-2) {}
  int get_definition();
 private:
  int def;
};

struct function;

struct ast_ident {
  std::string name;
  variable *var;
  function *fun;
  ast_ident(std::string const &s): name(s), var(NULL), fun(NULL) {}
  static ast_ident *find(std::string const &s);
  static ast_ident *temp();
};

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream, variable *value)
{
  stream << value->name->name;
  return stream;
}

struct function {
  ast_ident *name;
  int real_op;
  type_id *return_type;
  type_id *args_type;
  function(ast_ident *n, int r): name(n), real_op(r) {}
};

typedef std::vector< variable * > variable_vec;

struct instruction {
  function *fun;
  variable_vec in;
  variable_vec out;
};

typedef std::vector< instruction > program_t;
extern program_t program;

#endif // PROGRAM_HPP
