#include "real.hpp"
#include "float.hpp"
#include "ast.hpp"
#include <sstream>

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

static impl_data *read_number(ast_number const &n, interval_float_description *desc, mp_rnd_t rnd) {
  if (n.base == 0) return read_number_data(n, real_prec, rnd);
  impl_data *d;
  int p = real_prec, emin = -50000;
  if (desc) {
    p = desc->prec + 1;
    emin = desc->min_exp - p + 1; // 2^emin == smallest positive floating point number (subnormal)
  }
  for(;;) {
    d = read_number_data(n, p, rnd);
    if (mpfr_sgn(d->val) == 0) return d;
    int e = (d->val[0]._mpfr_exp - 1) - p + 1; // exponent of the least significative bit
    if (e >= emin) return d;
    delete d;
    p += e - emin;
  }
}

union float32_and_float {
  float32 soft;
  float hard;
};

union float64_and_double {
  float64 soft;
  double hard;
};

interval create_interval(ast_interval const &i, bool widen, type_id _type) {
  interval_float_description *type =
    _type == interval_real ? 0 :
    reinterpret_cast< interval_float_description * >(_type);
  mp_rnd_t d1 = widen ? GMP_RNDD : GMP_RNDU;
  mp_rnd_t d2 = widen ? GMP_RNDU : GMP_RNDD;
  impl_data *n1 = read_number(i.lower, type, d1);
  impl_data *n2 = read_number(i.upper, type, d2);
  interval res(_type, 0);
  if (_type == interval_real)
    res.ptr = new _interval_real(number_real(n1), number_real(n2));
  else {
    if (_type == interval_float32) {
      float32_and_float tmp1, tmp2;
      tmp1.hard = mpfr_get_d(n1->val, d1);
      tmp2.hard = mpfr_get_d(n2->val, d2);
      res.ptr = new _interval_float32(number_float32(tmp1.soft), number_float32(tmp2.soft));
    } else if (_type == interval_float64) {
      float64_and_double tmp1, tmp2;
      tmp1.hard = mpfr_get_d(n1->val, d1);
      tmp2.hard = mpfr_get_d(n2->val, d2);
      res.ptr = new _interval_float64(number_float64(tmp1.soft), number_float64(tmp2.soft));
    } else assert(false); /* TODO */
    n1->destroy();
    n2->destroy();
  }
  return res;
}

std::ostream &operator<<(std::ostream &stream, number_float32 const &value) {
  float32_and_float f;
  f.soft = value.value;
  stream << f.hard;
  return stream;
}

std::ostream &operator<<(std::ostream &stream, number_float64 const &value) {
  float64_and_double f;
  f.soft = value.value;
  stream << f.hard;
  return stream;
}

std::ostream &operator<<(std::ostream &, number_floatx80 const &) { throw; }
std::ostream &operator<<(std::ostream &, number_float128 const &) { throw; }
