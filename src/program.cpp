#include <algorithm>
#include "program.hpp"

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
