#include "numbers/interval.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include <algorithm>
#include <cassert>

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

bool float_format::rndU(rnd const &r) const {
  return r.g || r.s;
}

bool float_format::rndCE(rnd const &r) const {
  // the lower bit of the mantissa is not necessarily the ulp bit
  // but testing for it works since the guard bit can only be 1 if
  // the number was to precise and got truncated
  return r.g && (r.s || mpz_tstbit(r.m, 0));
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

void float_format::trunc(mpfr_t const &f, rnd &r, int &sign) const {
  r.s = r.g = false;
  split_exact(f, r.m, r.e, sign);
  if (sign == 0) return;
  int size = mpz_sizeinbase(r.m, 2);
  int dec = std::max(min_exp - r.e, size - (int)prec);
  if (dec <= 0) return;
  r.shr(dec);
}

void float_format::round(mpfr_t &f, rnd_fun g1, rnd_fun g2) const {
  rnd r;
  int s;
  trunc(f, r, s);
  if (s == 0) return;
  if ((this->*(s > 0 ? g1 : g2))(r)) succ(r.m, r.e);
  mpfr_set_prec(f, prec);
  int v = mpfr_set_z(f, r.m, GMP_RNDN);
  assert(v == 0);
  mpfr_mul_2si(f, f, r.e, GMP_RNDN);
  if (s < 0) mpfr_neg(f, f, GMP_RNDN);
}

number round_number(number const &f, float_format const *t, rounding_fun r) {
  if (!t) return f;
  number res = f;
  number_base *d = res.unique();
  (t->*r)(d->val);
  return res;
}

interval rounding_class::round                      (interval const &, std::string &) const { return interval(); }
interval rounding_class::enforce                    (interval const &, std::string &) const { return interval(); }
interval rounding_class::absolute_error_from_real   (interval const &, std::string &) const { return interval(); }
interval rounding_class::relative_error_from_real   (interval const &, std::string &) const { return interval(); }
interval rounding_class::absolute_error_from_rounded(interval const &, std::string &) const { return interval(); }
interval rounding_class::relative_error_from_rounded(interval const &, std::string &) const { return interval(); }
