#include "parser/ast.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"

struct homogen_rounding_class: function_class {
  interval he;
  homogen_rounding_class();
  virtual interval absolute_error_from_real(interval const &, std::string &) const;
  virtual std::string name() const { return "homogen80x"; }
};

homogen_rounding_class::homogen_rounding_class()
  : function_class(UOP_ID, TH_ABS_REA) {
  he = from_exponent(-53, 0) + from_exponent(-64, 0);
  new default_function_generator("homogen80x", this);
}

interval homogen_rounding_class::absolute_error_from_real(interval const &i, std::string &name) const {
  name = "homogen80x_error";
  return i * he;
}

static homogen_rounding_class dummy;

struct homogen_init_rounding_class: function_class {
  interval he;
  homogen_init_rounding_class();
  virtual interval absolute_error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const { return "homogen80x_init"; }
};

homogen_init_rounding_class::homogen_init_rounding_class()
  : function_class(UOP_ID, TH_ABS_RND) {
  he = from_exponent(-53, 0) + from_exponent(-64, 0);
  new default_function_generator("homogen80x_init", this);
}

interval homogen_init_rounding_class::absolute_error_from_rounded(interval const &i, std::string &name) const {
  name = "homogen80x_init_error";
  return i * he;
}

static homogen_init_rounding_class dummy_init;

struct floatx_rounding_class: function_class {
  floatx_rounding_class();
  virtual interval round(interval const &, std::string &) const;
  virtual std::string name() const { return "float80x"; }
};

floatx_rounding_class::floatx_rounding_class()
  : function_class(UOP_ID, TH_RND) {
  new default_function_generator("float80x", this);
}

struct floatx_format: gs_rounding {
  virtual int shift_val(int exp, int sz) const { return std::max(-1074 - exp, sz - 53); }
};

interval floatx_rounding_class::round(interval const &i, std::string &name) const {
  static floatx_format format;
  number a = round_number(lower(i), &format, &floatx_format::roundD);
  number b = round_number(upper(i), &format, &floatx_format::roundU);
  name = "float80x_round";
  return interval(a, b);
}

static floatx_rounding_class dummy2;
