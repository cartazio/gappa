#include <sstream>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"

static number read_number(ast_number const &n, mp_rnd_t rnd) {
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

interval create_interval(ast_interval const &i, bool widen) {
  mp_rnd_t d1 = widen ? GMP_RNDD : GMP_RNDU;
  mp_rnd_t d2 = widen ? GMP_RNDU : GMP_RNDD;
  return interval(read_number(*i.lower, d1), read_number(*i.upper, d2));
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
  int sgn;
  split_exact(f, frac, exp, sgn);
  zero = sgn == 0;
  std::string res = zero ? "0" : signed_lexical(frac, sgn < 0);
  mpz_clear(frac);
  return res;
}

std::string get_real_split(number const &f, int &exp, bool &zero) {
  return get_real_split(f.data->val, exp, zero);
}

bool detailed_io = false;

std::ostream &operator<<(std::ostream &stream, number const &value) {
  mpfr_t const &f = value.data->val;
  if (!detailed_io) {
    stream << mpfr_get_d(f, GMP_RNDN);
    return stream;
  }
  bool zero; int exp;
  std::string s = get_real_split(f, exp, zero);
  bool neg = s[0] == '-';
  stream << s;
  if (!zero && exp != 0) stream << 'b' << exp;
  else if (s.size() < 5U + neg) return stream;
  stream << " {" << mpfr_get_d(f, GMP_RNDN) << ", ";
  if (neg) stream << '-';
  mpfr_t g;
  mpfr_init2(g, 20);
  mpfr_abs(g, f, GMP_RNDN);
  mpfr_log2(g, g, GMP_RNDN);
  stream << "2^(" << mpfr_get_d(g, GMP_RNDN) << ")}";
  mpfr_clear(g);
  return stream;
}

std::ostream &operator<<(std::ostream &stream, interval const &u)
{
  assert(u.base);
  stream << '[' << lower(u) << ", " << upper(u) << ']';
  return stream;
}
