#include "parser/ast.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"

struct double_rounding_class: rounding_class {
  interval he, hb;
  double_rounding_class();
  virtual interval bound(interval const &, std::string &) const;
  virtual interval error_from_real(interval const &, std::string &) const;
  virtual interval error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const { return "ddouble"; }
};

double_rounding_class::double_rounding_class() {
  he = from_exponent(-100, 0);
  hb = from_exponent(0, 0) + he;
  ast_ident *n = ast_ident::find("ddouble");
  n->id_type = REAL_RND;
  n->rnd = this;
}

interval double_rounding_class::bound(interval const &i, std::string &name) const {
  name = "ddouble_bound";
  return i * hb;
}

interval double_rounding_class::error_from_real(interval const &i, std::string &name) const {
  name = "ddouble_error";
  return i * he;
}

interval double_rounding_class::error_from_rounded(interval const &i, std::string &name) const {
  name = "ddouble_error_inv";
  return i * he;
}

static double_rounding_class dummy;
