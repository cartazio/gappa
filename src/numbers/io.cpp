#include "real.hpp"
#include "float.hpp"
#include "ast.hpp"
#include <sstream>

static impl_data *read_number_data(ast_number const &n, int p, mp_rnd_t rnd) {
  impl_data *res = new impl_data;
  assert(p >= 2); // TODO
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

static impl_data *read_number(ast_number const &n, interval_float_description const *desc, mp_rnd_t rnd) {
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

static void store_float(void *mem, mpfr_t const &f, interval_float_description const *desc) { // TODO: little-endian centric
  int fmt = desc->format_size;
  int min_exp = desc->min_exp;
  int prec = desc->prec;
  bool implicit = prec != 63; // implicit leading digit
  memset(mem, 0, fmt >> 3);
  mpz_t frac;
  mpz_init(frac);
  int exp = mpfr_get_z_exp(frac, f);
  int sgn = mpz_sgn(frac);
  if (sgn == 0) exp = min_exp - 1;
  else {
    mpz_export(mem, 0, -1, 2, -1, 0, frac); // export does not consider the sign
    exp = exp + mpfr_get_prec(f) - 1; // normalize the exponent
    if (exp < min_exp) exp = min_exp - 1; // subnormal number
  }
  mpz_clear(frac);
  int exp_pos = prec + (implicit ? 0 : 1); // the exponent is after the mantissa
  int exp_size = fmt - exp_pos - 1; // all the space except the mantissa and the sign
  int mask = (1 << exp_size) - 1;
  exp = (exp + 1 - min_exp) & mask; // biased exponent
  short int &e = ((short int *)mem)[exp_pos >> 4]; // last word of the float
  exp_pos &= 15;
  if (implicit) e &= ~(1 << exp_pos); // remove implicit one
  e |= exp << exp_pos;
  if (sgn < 0) e |= 1 << 15; // sign
}

interval create_interval(ast_interval const &i, bool widen, type_id _type) {
  interval_float_description const *type =
    _type == interval_real ? 0 :
    reinterpret_cast< interval_float_description const * >(_type);
  mp_rnd_t d1 = widen ? GMP_RNDD : GMP_RNDU;
  mp_rnd_t d2 = widen ? GMP_RNDU : GMP_RNDD;
  impl_data *n1 = read_number(i.lower, type, d1);
  impl_data *n2 = read_number(i.upper, type, d2);
  interval res(_type, 0);
  if (_type == interval_real)
    res.ptr = new _interval_real(number_real(n1), number_real(n2));
  else {
    char tmp1[16], tmp2[16];
    store_float(&tmp1, n1->val, type);
    store_float(&tmp2, n2->val, type);
    if (_type == interval_float32)
      res.ptr = new _interval_float32(number_float32(*(float32 *)tmp1), number_float32(*(float32 *)tmp2));
    else if (_type == interval_float64)
      res.ptr = new _interval_float64(number_float64(*(float64 *)tmp1), number_float64(*(float64 *)tmp2));
    else if (_type == interval_floatx80)
      res.ptr = new _interval_floatx80(number_floatx80(*(floatx80 *)tmp1), number_floatx80(*(floatx80 *)tmp2));
    else if (_type == interval_float128)
      res.ptr = new _interval_float128(number_float128(*(float128 *)tmp1), number_float128(*(float128 *)tmp2));
    else assert(false);
    n1->destroy();
    n2->destroy();
  }
  return res;
}

void load_float(void const *_mem, mpfr_t &f, interval_float_description const *desc) { // TODO: little-endian centric
  void *mem = const_cast< void * >(_mem);
  int fmt = desc->format_size;
  int min_exp = desc->min_exp;
  int prec = desc->prec;
  bool implicit = prec != 63; // implicit leading digit
  int exp_pos = prec + (implicit ? 0 : 1); // the exponent is after the mantissa
  int exp_size = fmt - exp_pos - 1; // all the space except the mantissa and the sign
  int mask = (1 << exp_size) - 1;
  short int &e = ((short int *)mem)[exp_pos >> 4]; // last word of the float
  exp_pos &= 15;
  int exp = (e >> exp_pos) & mask;
  exp = exp + min_exp - 1; // biased exponent
  bool sgn = e >> 15;
  short int save_e = e;
  e &= (1 << exp_pos) - 1;
  if (implicit && exp >= min_exp) e |= 1 << exp_pos; // implicit one
  mpz_t frac;
  mpz_init(frac);
  mpz_import(frac, fmt >> 4, -1, 2, -1, 0, _mem);
  if (sgn) mpz_neg(frac, frac);
  mpf_t frac2;
  mpf_init(frac2);
  mpf_set_z(frac2, frac);
  mpz_clear(frac);
  mpf_mul_2exp(frac2, frac2, exp - prec);
  mpfr_set_f(f, frac2, GMP_RNDN);
  mpf_clear(frac2);
  e = save_e;
}

static void write_exact(std::ostream &stream, mpfr_t const &f) {
  int sgn = mpfr_sgn(f);
  if (sgn == 0) { stream << '0'; return; }
  mpz_t frac;
  mpz_init(frac);
  int exp = mpfr_get_z_exp(frac, f);
  if (sgn < 0) stream << '-'; // avoid an
  mpz_abs(frac, frac);        // MPFR bug
  int d = mpz_scan1(frac, 0);
  if (d > 0) mpz_fdiv_q_2exp(frac, frac, d);
  char *s = mpz_get_str(NULL, 10, frac);
  stream << s;
  free(s);
  mpz_clear(frac);
  exp += d;
  if (exp != 0) stream << 'b' << exp;
}

static void write_approx(std::ostream &stream, mpfr_t const &f) {
  stream << mpfr_get_d(f, GMP_RNDN);  
}

static void write_real(std::ostream &stream, impl_data const *data) {
  write_exact(stream, data->val);
  stream << " {";
  write_approx(stream, data->val);
  stream << '}';
}

#define OUTPUT(sz)	\
  std::ostream &operator<<(std::ostream &stream, number_float##sz const &value) {	\
    impl_data *d = new impl_data;	\
    load_float(&value.value, d->val, reinterpret_cast< interval_float_description const * >(interval_float##sz));	\
    write_real(stream, d);	\
    d->destroy();	\
    return stream;	\
  }

OUTPUT(32)
OUTPUT(64)
OUTPUT(x80)
OUTPUT(128)

std::ostream &operator<<(std::ostream &stream, number_real const &value) {
  write_real(stream, value.data);
  return stream;
}
