#include <map>
#include <sstream>
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"

struct fixed_rounding_class: function_class {
  int prec;
  fixed_rounding_class(int p): prec(p) {}
  virtual interval round                      (interval const &, std::string &) const;
  virtual interval absolute_error_from_real   (interval const &, std::string &) const;
  virtual interval absolute_error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const;
 private:
  number trunc(number const &) const;
};

number fixed_rounding_class::trunc(number const &n) const {
  mpz_t m;
  mpz_init(m);
  int s, e;
  split_exact(n.mpfr_data(), m, e, s);
  number res = n;
  if (e < prec) {
    mpz_fdiv_q_2exp(m, m, prec - e);
    mpfr_t &f = res.unique()->val;
    mpfr_set_prec(f, parameter_internal_precision);
    int v = mpfr_set_z(f, m, GMP_RNDN);
    assert(v == 0);
    mpfr_mul_2si(f, f, prec, GMP_RNDN);
    if (s < 0) mpfr_neg(f, f, GMP_RNDN);
  }
  mpz_clear(m);
  return res;
}

interval fixed_rounding_class::round(interval const &i, std::string &name) const {
  std::ostringstream s;
  s << "(fixed_error " << prec << ')';
  name = s.str();
  return interval(trunc(lower(i)), trunc(upper(i)));
}

interval fixed_rounding_class::absolute_error_from_real(interval const &i, std::string &name) const {
  std::ostringstream s;
  s << "(fixed_error " << prec << ')';
  name = s.str();
  if (lower(i) >= 0) return from_exponent(prec, -1);
  if (upper(i) <= 0) return from_exponent(prec, +1);
  return from_exponent(prec, 0);
}

interval fixed_rounding_class::absolute_error_from_rounded(interval const &i, std::string &name) const {
  std::ostringstream s;
  s << "(fixed_error " << prec << ')';
  name = s.str();
  if (lower(i) > 0) return from_exponent(prec, -1);
  if (upper(i) < 0) return from_exponent(prec, +1);
  return from_exponent(prec, 0);
}

std::string fixed_rounding_class::name() const {
  std::ostringstream s;
  s << "rounding_fixed " << prec;
  return s.str();
}

struct fixed_rounding_generator: function_generator {
  function_class const *fun;
  std::string rnd;
  fixed_rounding_generator();
  virtual function_class const *operator()(function_params const &) const;
};

fixed_rounding_generator::fixed_rounding_generator() {
  ast_ident *id = ast_ident::find("fixed");
  id->fun = this;
}

typedef std::map< int, function_class const * > fixed_cache;
static fixed_cache cache;

function_class const *fixed_rounding_generator::operator()(function_params const &p) const {
  int prec;
  if (p.size() != 1 || !param_int(p[0], prec)) return NULL;
  fixed_cache::const_iterator i = cache.find(prec);
  if (i != cache.end()) return i->second;
  function_class const *rnd = new fixed_rounding_class(prec);
  cache.insert(std::make_pair(prec, rnd));
  return rnd;
}

static fixed_rounding_generator dummy;
