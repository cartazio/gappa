#include <algorithm>
#include "program.hpp"

program_t program;

variable::variable(ast_ident *n, type_id t): name(n), type(t), def(-2) {
  real = new ast_real(this);
}

int variable::get_definition() {
  if (def != -2) return def;
  def = -1;
  for(int i = program.size() - 1; i >= 0; i--) {
    variable_vec const &out = program[i].out;
    if (std::find(out.begin(), out.end(), this) != out.end())
    { def = i; break; }
  }
  return def;
}
