#include "real.hpp"
#include "round.hpp"
#include "types.hpp"
#include <algorithm>
#include <cassert>

bool split_exact(mpfr_t const &f, mpz_t &frac, int &exp, bool &sign) { // return true if zero
  int sgn = mpfr_sgn(f);
  if (sgn == 0) return true;
  exp = mpfr_get_z_exp(frac, f);
  sign = (sgn < 0);
  mpz_abs(frac, frac); // avoid an MPFR bug
  int d = mpz_scan1(frac, 0);
  if (d > 0) mpz_fdiv_q_2exp(frac, frac, d);
  exp += d;
  return false;
}

void rnd::shr(int d) {
  assert(d >= 0);
  if (d == 0) return;
  e += d;
  if (!(g || s || d == 1))
    g = mpz_divisible_2exp_p(m, d - 1);
  else s |= g;
  g = mpz_tstbit(m, d - 1);
  mpz_tdiv_q_2exp(m, m, d);
}

bool float_format::rndU(rnd const &r) const {
  return r.g || r.s;
}

bool float_format::rndCE(rnd const &r) const {
  return r.g && (r.s || !mpz_tstbit(r.m, 0));
}

void float_format::succ(mpz_t &m, int &e) const {
  assert(mpz_sgn(m) >= 0 && mpz_sizeinbase(m, 2) <= prec && e >= min_exp);
  if (e > min_exp)
    mpz_mul_2exp(m, m, prec - mpz_sizeinbase(m, 2));
  mpz_add_ui(m, m, 1);
  if (mpz_sizeinbase(m, 2) > prec) {
    mpz_set_ui(m, 1);
    e += prec;
  }
}

void float_format::trunc(mpfr_t const &f, rnd &r, bool &sign) const {
  split_exact(f, r.m, r.e, sign);
  r.s = r.g = false;
  int size = mpz_sizeinbase(r.m, 2);
  int dec = std::max(min_exp - r.e, size - (int)prec);
  if (dec <= 0) return;
  r.shr(dec);
}

void float_format::round(mpfr_t &f, rnd_fun g1, rnd_fun g2) const {
  rnd r;
  bool s;
  trunc(f, r, s);
  if ((this->*(s ? g2 : g1))(r)) succ(r.m, r.e);
  mpfr_set_prec(f, prec);
  int v = mpfr_set_z(f, r.m, GMP_RNDN);
  assert(v == 0);
  mpfr_mul_2si(f, f, r.e, GMP_RNDN);
  if (s) mpfr_neg(f, f, GMP_RNDN);
}

number number_type::rounded_up(number const &f) const {
  if (!format) return f;
  number res = f;
  number_base *d = res.unique();
  format->roundU(d->val);
  return res;
}

number number_type::rounded_dn(number const &f) const {
  if (!format) return f;
  number res = f;
  number_base *d = res.unique();
  format->roundD(d->val);
  return number(d);
}
