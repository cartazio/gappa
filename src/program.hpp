#ifndef PROGRAM_HPP
#define PROGRAM_HPP

#include "ast_real.hpp"
#include "numbers/types.hpp"

#include <iostream>
#include <vector>

struct ast_ident;
struct instruction;
struct node;

typedef number_type const *type_id;

struct variable {
  ast_ident *name;
  ast_real *real;
  instruction *inst;
  type_id type;
  variable(ast_ident *n, type_id t = NULL);
};

struct function;

enum ident_type { UNKNOWN_ID, PROG_FUN, PROG_VAR, REAL_VAR };

struct ast_ident {
  std::string name;
  union {
    variable *var;
    function *fun;
    real_variable *rvar;
  };
  ident_type id_type;
  ast_ident(std::string const &s): name(s), id_type(UNKNOWN_ID) {}
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

struct bound_computation;
struct error_computation;

struct function {
  real_op_type type;
  type_id const *return_type;
  type_id const *args_type;
  bound_computation const *bnd_comp;
  error_computation const *err_comp;
  function(real_op_type t): type(t) {}
};

typedef std::vector< variable * > variable_vec;

struct instruction {
  function *fun;
  variable_vec in;
  variable_vec out;
};

typedef std::vector< instruction * > program_t;
extern program_t program;

#endif // PROGRAM_HPP
