#include "round.hpp"

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
