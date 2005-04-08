#include "parser/ast.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"

struct homogen_rounding_class: rounding_class {
  interval he, hb;
  homogen_rounding_class();
  virtual interval round                   (interval const &, std::string &) const;
  virtual interval absolute_error_from_real(interval const &, std::string &) const;
  virtual std::string name() const { return "homogen80x"; }
};

homogen_rounding_class::homogen_rounding_class() {
  he = from_exponent(-53, 0) + from_exponent(-64, 0);
  hb = from_exponent(0, 0) + he;
  ast_ident *n = ast_ident::find("homogen80x");
  n->id_type = REAL_RND;
  n->rnd = this;
}

interval homogen_rounding_class::round(interval const &i, std::string &name) const {
  name = "homogen80x_bound";
  return i * hb;
}

interval homogen_rounding_class::absolute_error_from_real(interval const &i, std::string &name) const {
  name = "homogen80x_error";
  return i * he;
}

static homogen_rounding_class dummy;

struct homogen_init_rounding_class: rounding_class {
  interval he;
  homogen_init_rounding_class();
  virtual interval absolute_error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const { return "homogen80x_init"; }
};

homogen_init_rounding_class::homogen_init_rounding_class() {
  he = from_exponent(-53, 0) + from_exponent(-64, 0);
  ast_ident *n = ast_ident::find("homogen80x_init");
  n->id_type = REAL_RND;
  n->rnd = this;
}

interval homogen_init_rounding_class::absolute_error_from_rounded(interval const &i, std::string &name) const {
  name = "homogen80x_init_error";
  return i * he;
}

static homogen_init_rounding_class dummy_init;
