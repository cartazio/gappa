#include <sstream>
#include "number_ext.hpp"
#include "ast.hpp"

static int const prec[] = { real_prec, 24, 53, 64, 113 };

impl_data *read_number(ast_number const &n, type_id type, mp_rnd_t rnd) {
  int p = prec[type];
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
