#ifndef PROGRAM_HPP
#define PROGRAM_HPP

#include <vector>
#include <iostream>
#include "types.hpp"
#include "ast_real.hpp"

struct ast_ident;
struct instruction;
struct node;

struct variable {
  ast_ident *name;
  ast_real *real;
  type_id type;
  variable(ast_ident *n, type_id t = UNDEFINED);
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

struct function_match;

struct function {
  real_op_type type;
  type_id const *return_type;
  type_id const *args_type;
  function_match const *matches;
  function(real_op_type t): type(t) {}
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
