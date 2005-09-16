#include <map>
#include <sstream>
#include "parser/ast.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"

struct dbldbl_function_class: function_class {
  interval he;
  int prec;
  std::string nm;
  dbldbl_function_class(real_op_type, int, std::string const &);
  virtual interval round                      (interval const &, std::string &) const;
  virtual interval relative_error_from_real   (interval const &, std::string &) const;
  virtual interval relative_error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const;
};

dbldbl_function_class::dbldbl_function_class(real_op_type t, int p, std::string const &n)
  : function_class(t), prec(p), nm(n) {
  he = from_exponent(-p, 0);
}

interval dbldbl_function_class::round(interval const &i, std::string &name) const {
  std::ostringstream s;
  s << '(' << nm << "_round " << prec << ')';
  name = s.str();
  return i * (interval(number(1), number(1)) + he);
}

interval dbldbl_function_class::relative_error_from_real(interval const &, std::string &name) const {
  std::ostringstream s;
  s << '(' << nm << "_error " << prec << ')';
  name = s.str();
  return he;
}

interval dbldbl_function_class::relative_error_from_rounded(interval const &, std::string &name) const {
  std::ostringstream s;
  s << '(' << nm << "_error_inv " << prec << ')';
  name = s.str();
  return he;
}

std::string dbldbl_function_class::name() const {
  std::ostringstream s;
  s << nm << "_function " << prec;
  return s.str();
}

struct dbldbl_function_generator: function_generator {
  function_class const *fun;
  std::string rnd;
  dbldbl_function_generator(std::string const &, real_op_type, std::string const &, int);
  virtual function_class const *operator()(function_params const &) const;
};

dbldbl_function_generator::dbldbl_function_generator(std::string const &n, real_op_type t, std::string const &r, int p)
  : rnd(r) {
  ast_ident *id = ast_ident::find(n);
  id->fun = this;
  fun = new dbldbl_function_class(t, p, n);
}

function_class const *dbldbl_function_generator::operator()(function_params const &p) const {
  if (p.size() != 1) return NULL;
  ast_ident const *i = param_ident(p[0]);
  return (i && i->name == rnd) ? fun : NULL;
}

static dbldbl_function_generator dummy("add22", BOP_ADD, "float64ne", 103);
