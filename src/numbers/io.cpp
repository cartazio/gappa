#include "../ast.hpp"
#include "float.hpp"
#include "interval_utility.hpp"
#include "real.hpp"
#include "round.hpp"
#include "types.hpp"
#include <sstream>

static number_base *read_number(ast_number const &n, mp_rnd_t rnd) {
  number_base *res = new number_base;
  switch (n.base) {
  case 10: {
    std::stringstream s;
    s << n.mantissa << 'e' << n.exponent;
    mpfr_set_str(res->val, s.str().c_str(), 10, rnd);
    break; }
  case 2: {
    mpfr_set_str(res->val, n.mantissa.c_str(), 10, rnd);
    mpfr_mul_2si(res->val, res->val, n.exponent, rnd);
    break; }
  case 0: {
    mpfr_set_ui(res->val, 0, rnd);
    break; }
  default:
    assert(false);
  }
  return res;
}

interval create_interval(ast_interval const &i, bool widen, number_type const &type) {
  mp_rnd_t d1 = widen ? GMP_RNDD : GMP_RNDU;
  mp_rnd_t d2 = widen ? GMP_RNDU : GMP_RNDD;
  number_base *n1 = read_number(*i.lower, d1);
  number_base *n2 = read_number(*i.upper, d2);
  return interval(type.rounded_up(number(n1)), type.rounded_dn(number(n2)));
}

static std::string signed_lexical(mpz_t const &frac, bool sgn) {
  std::string res;
  if (sgn) res = '-';
  char *s = mpz_get_str(NULL, 10, frac);
  res += s;
  free(s);
  return res;
}

static std::string get_real_split(mpfr_t const &f, int &exp, bool &zero) {
  mpz_t frac;
  mpz_init(frac);
  bool sgn;
  zero = split_exact(f, frac, exp, sgn);
  std::string res = zero ? "0" : signed_lexical(frac, sgn);
  mpz_clear(frac);
  return res;
}

std::string get_real_split(number const &f, int &exp, bool &zero) {
  return get_real_split(f.data->val, exp, zero);
}

static void write_exact(std::ostream &stream, mpfr_t const &f) {
  bool zero;
  int exp;
  stream << get_real_split(f, exp, zero);
  if (!zero && exp != 0) stream << 'b' << exp;
}

static void write_approx(std::ostream &stream, mpfr_t const &f) {
  stream << mpfr_get_d(f, GMP_RNDN);  
}

static void write_real(std::ostream &stream, number_base const *data) {
  write_exact(stream, data->val);
  stream << " {";
  write_approx(stream, data->val);
  stream << '}';
}

std::ostream &operator<<(std::ostream &stream, number const &value) {
  write_real(stream, value.data);
  return stream;
}

std::ostream &operator<<(std::ostream &stream, interval const &u)
{
  assert(u.base);
  stream << '[' << lower(u) << ", " << upper(u) << ']';
  return stream;
}
