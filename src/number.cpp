#include <sstream>
#include <iostream>
#include <boost/numeric/interval/utility.hpp>
#include "number.hpp"
#include "number_ext.hpp"
#include "interval.hpp"
#include "ast.hpp"

number_real::number_real(int v) {
  impl_data *d = new impl_data;
  int r = mpfr_set_si(d->val, v, GMP_RNDN);
  assert(r == 0); (void)r;
  data = d;
}

bool number_real::operator<=(number_real const &v) const {
  if (mpfr_nan_p(data->val) || mpfr_nan_p(v.data->val)) return false;
  return mpfr_cmp(data->val, v.data->val) <= 0;
}

number_real const &min(number_real const &x, number_real const &y)
{ return (x <= y) ? x : y; }

number_real const &max(number_real const &x, number_real const &y)
{ return (x <= y) ? y : x; }

static impl_data *read_number(ast_number const &n, mp_prec_t p, mp_rnd_t r) {
  impl_data *res = new impl_data;
  mpfr_set_prec(res->val, p);
  if (n.base == 10) {
    std::stringstream s;
    s << n.mantissa << 'e' << n.exponent;
    mpfr_set_str(res->val, s.str().c_str(), 10, r);
  } else if (n.base == 2) {
    mpfr_set_str(res->val, n.mantissa.c_str(), 10, r);
    mpfr_mul_2si(res->val, res->val, n.exponent, r);
  } else {
    assert(n.base == 0);
    mpfr_set_ui(res->val, 0, r);
  }
  return res;
}

number_real to_real(number_float32 const &v) {
  impl_data *res = new impl_data;
  float32_and_float f;
  f.soft = v.value;
  int r = mpfr_set_d(res->val, f.hard, GMP_RNDN);
  assert(r == 0);
  return res;
}

union float32_inside {
  struct {
    unsigned int mantissa:23;
    unsigned int exponent:8;
    unsigned int negative:1;
  };
  float32 value;
};

int ulp_exponent(number_float32 const &v) {
  float32_inside f;
  f.value = v.value;
  int e = f.exponent;
  return ((e == 0) ? -126 : e - 127) - 23;
}

static int const prec[] = { real_prec, 24, 53, 64, 113 };

interval::interval(ast_interval const &i, bool widen, type_id type) {
  mp_rnd_t d1 = widen ? GMP_RNDD : GMP_RNDU;
  mp_rnd_t d2 = widen ? GMP_RNDU : GMP_RNDD;
  impl_data *n1 = read_number(i.lower, prec[type], d1);
  impl_data *n2 = read_number(i.upper, prec[type], d2);
  if (type == UNDEFINED)
    value = interval_real(number_real(n1), number_real(n2));
  else {
    if (type == FLOAT32) {
      float32_and_float tmp1, tmp2; /* TODO: underflow and overflow, mort a mpfr */
      tmp1.hard = mpfr_get_d(n1->val, d1);
      tmp2.hard = mpfr_get_d(n2->val, d2);
      value = interval_float32(number_float32(tmp1.soft), number_float32(tmp2.soft));
    } else if (type == FLOAT64) {
      float64_and_double tmp1, tmp2;
      tmp1.hard = mpfr_get_d(n1->val, d1);
      tmp2.hard = mpfr_get_d(n2->val, d2);
      value = interval_float64(number_float64(tmp1.soft), number_float64(tmp2.soft));
    } else assert(false); /* TODO */
    n1->destroy();
    n2->destroy();
  }
}

namespace {
struct do_add: boost::static_visitor< interval > {
  template< typename T, typename U >
  interval operator()(T const &, U const &) const { throw; /* TODO */ }
  template< typename T >
  typename boost::disable_if< boost::is_same< T, interval_not_defined >, interval >::type // interval
  operator()(T const &lhs, T const &rhs) const {
    return interval_variant(lhs + rhs);
  }
};

struct do_mul: boost::static_visitor< interval > {
  template< typename T, typename U >
  interval operator()(T const &, U const &) const { throw; /* TODO */ }
  template< typename T >
  typename boost::disable_if< boost::is_same< T, interval_not_defined >, interval >::type // interval
  operator()(T const &lhs, T const &rhs) const {
    return interval_variant(lhs * rhs);
  }
};

struct do_subset_of: boost::static_visitor< bool > {
  template< typename T >
  bool operator()(T const &, interval_not_defined const &) const { return true; }
  template< typename T, typename U >
  typename boost::disable_if< boost::is_same< U, interval_not_defined >, bool >::type // bool
  operator()(T const &, U const &) const { return false; /* TODO */ }
  template< typename T >
  typename boost::disable_if< boost::is_same< T, interval_not_defined >, bool >::type // bool
  operator()(T const &lhs, T const &rhs) const {
    return subset(lhs, rhs);
  }
};

struct do_to_real: boost::static_visitor< interval_real > {
  interval_real operator ()(interval_float32 const &v) const {
    return interval_real(to_real(lower(v)), to_real(upper(v)));
  }
  template< typename T >
  interval_real operator()(T const &) const { throw; }
};

struct do_exponent: boost::static_visitor< int > {
  int operator ()(interval_float32 const &v) const {
    return ulp_exponent(norm(v));
  }
  template< typename T >
  int operator()(T const &) const { throw; }
};

template< class CharType, class CharTraits >
struct do_output: boost::static_visitor< void > {
  typedef std::basic_ostream< CharType, CharTraits > ostream;
  ostream &stream;
  do_output(ostream &s): stream(s) {}
  void operator ()(interval_float32 const &v) const { stream << v; }
  void operator ()(interval_float64 const &v) const { stream << v; }
  void operator ()(interval_real const &v) const { stream << v; }
  void operator ()(interval_not_defined const &) const { stream << '?'; }
  template< typename T >
  void operator()(T const &) const { throw; }
};
}

interval interval::operator+(interval const &v) const { return boost::apply_visitor(do_add(), value, v.value); }
interval interval::operator*(interval const &v) const { return boost::apply_visitor(do_mul(), value, v.value); }
bool interval::operator<=(interval const &v) const { return boost::apply_visitor(do_subset_of(), value, v.value); }
interval to_real(interval const &v) { return interval_variant(boost::apply_visitor(do_to_real(), v.value)); }
int ulp_exponent(interval const &v) { return boost::apply_visitor(do_exponent(), v.value); }

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream, interval const &v)
{ boost::apply_visitor(do_output< CharType, CharTraits >(stream), v.value); return stream; }

void blop(interval const &v) { std::cout << v; }

interval from_exponent(int e, mp_rnd_t r) {
  assert(r == GMP_RNDN);
  impl_data *l = new impl_data, *u = new impl_data;
  mpfr_set_ui(u->val, 1, GMP_RNDN);
  mpfr_mul_2si(u->val, u->val, e - 1, GMP_RNDN);
  mpfr_neg(l->val, u->val, GMP_RNDN);
  return interval_variant(interval_real(number_real(l), number_real(u)));
}
