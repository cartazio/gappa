#include <map>
#include <sstream>
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"

struct fixed_format: gs_rounding {
  int min_exp;
  virtual int shift_val(int exp, int) const { return min_exp - exp; }
  fixed_format() {}
  fixed_format(int e): min_exp(e) {}
};

struct fixed_rounding_class: function_class {
  fixed_format format;
  direction_type type;
  std::string ident;
  fixed_rounding_class(fixed_format const &f, direction_type t, std::string const &i)
    : format(f), type(t), ident(i) {}
  virtual interval round                      (interval const &, std::string &) const;
  virtual interval enforce                    (interval const &, std::string &) const;
  virtual interval absolute_error_from_real   (interval const &, std::string &) const;
  virtual interval absolute_error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const { return "rounding_fixed " + ident; }
};

interval fixed_rounding_class::enforce(interval const &i, std::string &name) const {
  number a = round_number(lower(i), &format, &fixed_format::roundU);
  number b = round_number(upper(i), &format, &fixed_format::roundD);
  if (!(a <= b)) return interval();
  name = "(fixed_enforce" + ident + ')';
  return interval(a, b);
}

interval fixed_rounding_class::round(interval const &i, std::string &name) const {
  rounding_fun f = direction_functions[type];
  number a = round_number(lower(i), &format, f);
  number b = round_number(upper(i), &format, f);
  name = "(fixed_round" + ident + ')';
  return interval(a, b);
}

interval fixed_rounding_class::absolute_error_from_real(interval const &i, std::string &name) const {
  name = "(fixed_error" + ident + ')';
  if (type == ROUND_DN || type == ROUND_ZR && lower(i) >= 0) return from_exponent(format.min_exp, -1);
  if (type == ROUND_UP || type == ROUND_ZR && upper(i) <= 0) return from_exponent(format.min_exp, +1);
  return from_exponent(type == ROUND_ZR ? format.min_exp : format.min_exp - 1, 0);
}

interval fixed_rounding_class::absolute_error_from_rounded(interval const &i, std::string &name) const {
  name = "(fixed_error_inv" + ident + ')';
  if (type == ROUND_DN || type == ROUND_ZR && lower(i) > 0) return from_exponent(format.min_exp, -1);
  if (type == ROUND_UP || type == ROUND_ZR && upper(i) < 0) return from_exponent(format.min_exp, +1);
  return from_exponent(type == ROUND_ZR ? format.min_exp : format.min_exp - 1, 0);
}

struct fixed_rounding_generator: function_generator {
  fixed_rounding_generator();
  virtual function_class const *operator()(function_params const &) const;
};

fixed_rounding_generator::fixed_rounding_generator() {
  ast_ident *id = ast_ident::find("fixed");
  id->fun = this;
}

typedef std::map< int, fixed_rounding_class > fixed_cache;
static fixed_cache cache;

function_class const *fixed_rounding_generator::operator()(function_params const &p) const {
  fixed_format f;
  if (p.size() != 2 || !param_int(p[0], f.min_exp)) return NULL;
  direction_type d = get_direction(p[1]);
  if (d == ROUND_ARGL) return NULL;
  int h = (f.min_exp << 8) | (int)d;
  fixed_cache::const_iterator i = cache.find(h);
  if (i != cache.end()) return &i->second;
  std::ostringstream s;
  s << '_' << direction_names[d] << " (" << f.min_exp << ')';
  i = cache.insert(std::make_pair(h, fixed_rounding_class(f, d, s.str()))).first;
  return &i->second;
}

static fixed_rounding_generator dummy;
