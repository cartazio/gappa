#include <iostream>
#include <boost/numeric/interval/utility.hpp>
#include "interval.hpp"
#include "number_ext.hpp"
#include "interval.hpp"
#include "ast.hpp"

interval::interval(ast_interval const &i, bool widen, type_id type) {
  mp_rnd_t d1 = widen ? GMP_RNDD : GMP_RNDU;
  mp_rnd_t d2 = widen ? GMP_RNDU : GMP_RNDD;
  impl_data *n1 = read_number(i.lower, type, d1);
  impl_data *n2 = read_number(i.upper, type, d2);
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

struct do_sub: boost::static_visitor< interval > {
  template< typename T, typename U >
  interval operator()(T const &, U const &) const { throw; /* TODO */ }
  template< typename T >
  typename boost::disable_if< boost::is_same< T, interval_not_defined >, interval >::type // interval
  operator()(T const &lhs, T const &rhs) const {
    return interval_variant(lhs - rhs);
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
interval interval::operator-(interval const &v) const { return boost::apply_visitor(do_sub(), value, v.value); }
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
