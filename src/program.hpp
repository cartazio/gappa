#ifndef PROGRAM_HPP
#define PROGRAM_HPP

#include "ast_real.hpp"
#include "numbers/types.hpp"

#include <iostream>
#include <vector>

struct ast_ident;
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

struct bound_computation;
struct error_computation;

struct function {
  real_op_type type;
  bound_computation const *bnd_comp;
  error_computation const *err_comp;
  function(real_op_type t): type(t) {}
};

#endif // PROGRAM_HPP
