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

class float_format {
  void succ(mpz_t &m, int &e) const;
  void trunc(mpfr_t const &f, rnd &r, int &sign) const;
  typedef bool (float_format::*rnd_fun)(rnd const &) const;
  void round(mpfr_t &f, rnd_fun g1, rnd_fun g2) const;
  bool rndZ(rnd const &) const { return false; }
  bool rndU(rnd const &) const;
  bool rndCE(rnd const &) const;
 public:
  int min_exp;
  unsigned prec;
  void roundZ(mpfr_t &f) const { round(f, &float_format::rndZ, &float_format::rndZ); }
  void roundU(mpfr_t &f) const { round(f, &float_format::rndU, &float_format::rndZ); }
  void roundD(mpfr_t &f) const { round(f, &float_format::rndZ, &float_format::rndU); }
  void roundCE(mpfr_t &f) const { round(f, &float_format::rndCE, &float_format::rndCE); }
};

struct number;
struct interval;

typedef void (float_format::*rounding_fun)(mpfr_t &) const;
number round_number(number const &, float_format const *, rounding_fun);

struct rounding_class {
  virtual interval bound(interval const &, std::string &) const = 0;
  virtual interval error(interval const &, std::string &) const = 0;
  virtual std::string name() const = 0;
  virtual ~rounding_class() {}
};

#endif // NUMBERS_ROUND_HPP
