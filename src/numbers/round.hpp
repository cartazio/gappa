#ifndef NUMBERS_ROUND_HPP
#define NUMBERS_ROUND_HPP

#include <gmp.h>
#include <mpfr.h>
#include <string>

void split_exact(mpfr_t const &f, mpz_t &frac, int &exp, int &sign);

struct rnd {
  mpz_t m;
  int e;
  bool g, s;
  rnd() { mpz_init(m); }
  ~rnd() { mpz_clear(m); }
  void shr(int d);
};

class gs_rounding {
  void succ(mpz_t &m, int &e) const;
  void trunc(mpfr_t const &f, rnd &r, int &sign) const;
  typedef bool (gs_rounding::*rnd_fun)(rnd const &) const;
  void round(mpfr_t &f, rnd_fun g1, rnd_fun g2) const;
  bool rndZ(rnd const &) const { return false; }
  bool rndU(rnd const &) const;
  bool rndNE(rnd const &) const;
 protected:
  virtual int shift_val(int, int) const = 0;
 public:
  void roundZ(mpfr_t &f) const { round(f, &gs_rounding::rndZ, &gs_rounding::rndZ); }
  void roundU(mpfr_t &f) const { round(f, &gs_rounding::rndU, &gs_rounding::rndZ); }
  void roundD(mpfr_t &f) const { round(f, &gs_rounding::rndZ, &gs_rounding::rndU); }
  void roundNE(mpfr_t &f) const { round(f, &gs_rounding::rndNE, &gs_rounding::rndNE); }
  virtual ~gs_rounding() {}
};

struct number;
struct interval;

typedef void (gs_rounding::*rounding_fun)(mpfr_t &) const;
number round_number(number const &, gs_rounding const *, rounding_fun);

#endif // NUMBERS_ROUND_HPP
