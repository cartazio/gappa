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
  void round(mpfr_t &, rnd_fun, rnd_fun) const;
  bool rndZR(rnd const &) const { return false; }
  bool rndAW(rnd const &) const;
  bool rndNE(rnd const &) const;
  bool rndNO(rnd const &) const;
  bool rndNZ(rnd const &) const;
  bool rndNA(rnd const &) const;
  bool rndOD(rnd const &) const;
 protected:
  virtual int shift_val(int, int) const = 0;
 public:
  void roundUP(mpfr_t &f) const { round(f, &gs_rounding::rndZR, &gs_rounding::rndAW); }
  void roundDN(mpfr_t &f) const { round(f, &gs_rounding::rndAW, &gs_rounding::rndZR); }
  void roundZR(mpfr_t &f) const { round(f, &gs_rounding::rndZR, &gs_rounding::rndZR); }
  void roundAW(mpfr_t &f) const { round(f, &gs_rounding::rndAW, &gs_rounding::rndAW); }
  void roundOD(mpfr_t &f) const { round(f, &gs_rounding::rndOD, &gs_rounding::rndOD); }
  void roundNE(mpfr_t &f) const { round(f, &gs_rounding::rndNE, &gs_rounding::rndNE); }
  void roundNO(mpfr_t &f) const { round(f, &gs_rounding::rndNO, &gs_rounding::rndNO); }
  void roundNZ(mpfr_t &f) const { round(f, &gs_rounding::rndNZ, &gs_rounding::rndNZ); }
  void roundNA(mpfr_t &f) const { round(f, &gs_rounding::rndNA, &gs_rounding::rndNA); }
  void roundNU(mpfr_t &f) const { round(f, &gs_rounding::rndNZ, &gs_rounding::rndNA); }
  void roundND(mpfr_t &f) const { round(f, &gs_rounding::rndNA, &gs_rounding::rndNZ); }
  virtual ~gs_rounding() {}
};

struct number;
struct interval;

typedef void (gs_rounding::*rounding_fun)(mpfr_t &) const;
number round_number(number const &, gs_rounding const *, rounding_fun);
number simplify(number const &, int);

enum direction_type { ROUND_UP, ROUND_DN, ROUND_ZR, ROUND_AW, ROUND_OD,
                      ROUND_NE, ROUND_NO, ROUND_NZ, ROUND_NA, ROUND_NU, ROUND_ND,
                      ROUND_ARGL = -1 };
static int const nb_directions = 11;
extern char const *direction_names[nb_directions];
extern rounding_fun direction_functions[nb_directions];
direction_type get_direction(unsigned long);

int rnd_global_direction_abs(direction_type);
int rnd_global_direction_rel(direction_type);
int rnd_global_direction_abs(direction_type, interval const &);
int rnd_global_direction_rel(direction_type, interval const &);
inline bool rnd_to_nearest(direction_type type) { return type >= ROUND_NE; }
int rnd_influence_direction(direction_type, bool);

#endif // NUMBERS_ROUND_HPP
