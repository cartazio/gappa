#include <algorithm>
#include <cassert>
#include <map>
#include "utils.hpp"
#include "numbers/interval.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"

void split_exact(mpfr_t const &f, mpz_t &frac, int &exp, int &sign) {
  sign = mpfr_sgn(f);
  if (sign == 0) return;
  exp = mpfr_get_z_exp(frac, f);
  mpz_abs(frac, frac); // avoid an MPFR bug
  int d = mpz_scan1(frac, 0);
  if (d > 0) mpz_fdiv_q_2exp(frac, frac, d);
  exp += d;
}

void rnd::shr(int d) {
  assert(d >= 0);
  if (d == 0) return;
  e += d;
  if (!(g || s || d == 1))
    s = !mpz_divisible_2exp_p(m, d - 1);
  else s |= g;
  g = mpz_tstbit(m, d - 1);
  mpz_tdiv_q_2exp(m, m, d);
}

// The lower bit of the mantissa is not necessarily the ulp bit. But testing
// for it in conjunction with the guard bit or the sticky bit works. Otherwise
// the number was not truncated and it does not have to be changed.

bool gs_rounding::rndAW(rnd const &r) const {
  return r.g || r.s;
}

bool gs_rounding::rndNE(rnd const &r) const {
  return r.g && (r.s || mpz_tstbit(r.m, 0));
}

bool gs_rounding::rndNO(rnd const &r) const {
  return r.g && (r.s || !mpz_tstbit(r.m, 0));
}

bool gs_rounding::rndNZ(rnd const &r) const {
  return r.g && r.s;
}

bool gs_rounding::rndNA(rnd const &r) const {
  return r.g;
}

bool gs_rounding::rndOD(rnd const &r) const {
  return (r.g || r.s) && !mpz_tstbit(r.m, 0);
}

void gs_rounding::succ(mpz_t &m, int &e) const {
  assert(mpz_sgn(m) >= 0);
  int dec = shift_val(e, mpz_sizeinbase(m, 2));
  assert(dec >= 0);
  if (dec > 0) {
    mpz_mul_2exp(m, m, dec);
    e -= dec;
  }
  mpz_add_ui(m, m, 1);
  dec = mpz_scan1(m, 0);
  if (dec > 0) mpz_fdiv_q_2exp(m, m, dec);
  e += dec;
}

void gs_rounding::trunc(mpfr_t const &f, rnd &r, int &sign) const {
  r.s = r.g = false;
  split_exact(f, r.m, r.e, sign);
  if (sign == 0) return;
  int dec = shift_val(r.e, mpz_sizeinbase(r.m, 2));
  if (dec <= 0) return;
  r.shr(dec);
}

void gs_rounding::round(mpfr_t &f, rnd_fun g_neg, rnd_fun g_pos) const {
  rnd r;
  int s;
  trunc(f, r, s);
  if (s == 0) return;
  if ((this->*(s > 0 ? g_pos : g_neg))(r)) succ(r.m, r.e);
  mpfr_set_prec(f, std::max<int>(mpz_sizeinbase(r.m, 2), 2));
  int v = mpfr_set_z(f, r.m, GMP_RNDN);
  assert(v == 0);
  mpfr_mul_2si(f, f, r.e, GMP_RNDN);
  if (s < 0) mpfr_neg(f, f, GMP_RNDN);
}

number round_number(number const &f, gs_rounding const *t, rounding_fun r) {
  if (!t) return f;
  number res = f;
  number_base *d = res.unique();
  (t->*r)(d->val);
  return res;
}

typedef std::map< ast_ident const *, direction_type > rounding_directions;
static rounding_directions directions;
rounding_fun direction_functions[nb_directions];
char const *direction_names[nb_directions];

#define REGISTER_DIRECTION(name, type) \
  directions.insert(std::make_pair(ast_ident::find(#name), ROUND_##type)); \
  direction_functions[ROUND_##type] = &gs_rounding::round##type; \
  direction_names[ROUND_##type] = #name

RUN_ONCE(register_directions) {
  REGISTER_DIRECTION(up, UP);
  REGISTER_DIRECTION(dn, DN);
  REGISTER_DIRECTION(zr, ZR);
  REGISTER_DIRECTION(ne, NE);
}

direction_type get_direction(unsigned long u) {
  rounding_directions::const_iterator i = directions.find(param_ident(u));
  if (i == directions.end()) return ROUND_ARGL;
  return i->second;
}
