#include <sstream>
#include "number_ext.hpp"
#include "ast.hpp"

static impl_data *read_number_data(ast_number const &n, int p, mp_rnd_t rnd) {
  impl_data *res = new impl_data;
  mpfr_set_prec(res->val, p);
  if (n.base == 10) {
    std::stringstream s;
    s << n.mantissa << 'e' << n.exponent;
    mpfr_set_str(res->val, s.str().c_str(), 10, rnd);
  } else if (n.base == 2) {
    mpfr_set_str(res->val, n.mantissa.c_str(), 10, rnd);
    mpfr_mul_2si(res->val, res->val, n.exponent, rnd);
  } else {
    assert(n.base == 0);
    mpfr_set_ui(res->val, 0, rnd);
  }
  return res;
}

static int const prec[] = { real_prec, 24, 53, 64, 113 };
static int const min_exp[] = { mpfr_get_emin(), -126, -1022, -16382, -16382 };

impl_data *read_number(ast_number const &n, type_id type, mp_rnd_t rnd) {
  if (n.base == 0) return read_number_data(n, real_prec, rnd);
  impl_data *d;
  int p = prec[type];
  int emin = min_exp[type] - p + 1; // 2^emin == smallest positive floating point number (subnormal)
  for(;;) {
    d = read_number_data(n, p, rnd);
    if (mpfr_sgn(d->val) == 0) return d;
    int e = (d->val[0]._mpfr_exp - 1) - p + 1; // exponent of the least significative bit
    if (e >= emin) return d;
    delete d;
    p += e - emin;
  }
}
