#include <algorithm>
#include "program.hpp"

program_t program;

variable::variable(ast_ident *n, type_id t): name(n), inst(NULL), type(t) {
  assert(n->id_type = PROG_VAR);
  real = normalize(ast_real(this));
}
