#include "float.hpp"
#include "real.hpp"
#include <boost/numeric/interval/arith.hpp>
#include <boost/numeric/interval/utility.hpp>

namespace boost {
namespace numeric {
template< class T, class Policies >
T mig(interval< T, Policies > const &v) { using std::max; return max(T(0), max(v.lower(), -v.upper())); }
} // namespace numeric
} // namespace boost

std::ostream &operator<<(std::ostream &, number_float32 const &);
std::ostream &operator<<(std::ostream &, number_float64 const &);
std::ostream &operator<<(std::ostream &, number_floatx80 const &);
std::ostream &operator<<(std::ostream &, number_float128 const &);

template<class T, class Policies>
std::ostream &operator<<(std::ostream &stream, const boost::numeric::interval<T, Policies> &value) {
  if (empty(value)) {
    return stream << "[]";
  } else if (singleton(value)) {
    return stream << '[' << lower(value) << ']';
  } else {
    return stream << '[' << lower(value) << ',' << upper(value) << ']';
  }
}

namespace {

union float32_inside {
  struct {
    unsigned int mantissa:23;
    unsigned int exponent:8;
    unsigned int negative:1;
  };
  float32 value;
};

static int exponent(number_float32 const &v) {
  float32_inside f;
  f.value = v.value;
  int e = f.exponent;
  return (e == 0) ? -126 : e - 127;
}

union float64_inside {
  struct {
    unsigned long long int mantissa:52;
    unsigned long long int exponent:11;
    unsigned long long int negative:1;
  };
  float64 value;
};

static int exponent(number_float64 const &v) {
  float64_inside f;
  f.value = v.value;
  int e = f.exponent;
  return (e == 0) ? -1022 : e - 1023;
}

union floatx80_inside {
  struct {
    unsigned int exponent:15;
    unsigned int negative:1;
  };
  unsigned int value;
};

static int exponent(number_floatx80 const &v) {
  floatx80_inside f;
  f.value = v.value.high;
  int e = f.exponent;
  return (e == 0) ? -16382 : e - 16383;
}

union float128_inside {
  struct {
    unsigned long long int mantissa2:48;
    unsigned long long int exponent:15;
    unsigned long long int negative:1;
  };
  unsigned long long int value;
};

static int exponent(number_float128 const &v) {
  float128_inside f;
  f.value = v.value.high;
  int e = f.exponent;
  return (e == 0) ? -16382 : e - 16383;
}

static void split(number_float32 &u, number_float32 &v) {
  static float32 half = 126 << 23;
  float32 m = float32_mul(float32_add(u.value, v.value), half);
  if (m == u.value || m == v.value) return;
  float32 n = m + 1; // n is near m since m != 0xFF..F (NaN), below if m is negative
  if (m & (1 << 31)) { u.value = n; v.value = m; } else { u.value = m; v.value = n; }
}

static void split(number_float64 &, number_float64 &) { throw; }
static void split(number_floatx80 &, number_floatx80 &) { throw; }
static void split(number_float128 &, number_float128 &) { throw; }

union float32_and_float {
  float32 soft;
  float hard;
};

union float64_and_double {
  float64 soft;
  double hard;
};

static number_real to_real(number_float32 const &v) {
  impl_data *res = new impl_data;
  float32_and_float f;
  f.soft = v.value;
  int r = mpfr_set_d(res->val, f.hard, GMP_RNDN);
  assert(r == 0);
  return res;
}

static number_real to_real(number_float64 const &v) {
  impl_data *res = new impl_data;
  float64_and_double f;
  f.soft = v.value;
  int r = mpfr_set_d(res->val, f.hard, GMP_RNDN);
  assert(r == 0);
  return res;
}

static number_real to_real(number_floatx80 const &) { throw; }
static number_real to_real(number_float128 const &) { throw; }

} // anonymous namespace

#define pcast(sz,p) static_cast< _interval_float##sz * >(p)
#define cast(sz,p) *static_cast< _interval_float##sz * >(p)
#define gen(sz,p) new _interval_float##sz(p)
#define gen2(sz,p,q) new _interval_float##sz(p,q)

#define INTERVAL_FLOAT(sz, _prec, _min, _fmt_sz)		\
  static void *create_##sz() { return new _interval_float##sz; }		\
  static void destroy_##sz(void *v) { delete pcast(sz,v); }			\
  static void *clone_##sz(void *v) { return gen(sz, cast(sz,v)); }	\
  static void *add_##sz(void *u, void *v) { return gen(sz, cast(sz,u) + cast(sz,v)); }	\
  static void *sub_##sz(void *u, void *v) { return gen(sz, cast(sz,u) - cast(sz,v)); }	\
  static void *mul_##sz(void *u, void *v) { return gen(sz, cast(sz,u) * cast(sz,v)); }	\
  static void *div_##sz(void *u, void *v) { return gen(sz, cast(sz,u) / cast(sz,v)); }	\
  static bool subset_##sz(void *u, void *v) { return subset(cast(sz,u), cast(sz,v)); }	\
  static bool singleton_##sz(void *v) { return singleton(cast(sz,v)); }	\
  static bool zero_##sz(void *v) { return in_zero(cast(sz,v)); }	\
  static void *real_##sz(void *v) { return new _interval_real(to_real(lower(cast(sz,v))), to_real(upper(cast(sz,v)))); }	\
  static void *hull_##sz(void *u, void *v) { return gen(sz, hull(cast(sz,u), cast(sz,v))); }	\
  static std::pair< void *, void * > split_##sz(void *v)	\
  { number_float##sz const &l = lower(cast(sz,v)), &u = upper(cast(sz,v)); number_float##sz a = l, b = u;	\
    split(a, b); return std::make_pair(gen2(sz,l,a), gen2(sz,b,u)); }	\
  static void output_##sz(std::ostream &s, void *v) { s << cast(sz,v); }	\
  static int mig_exp_##sz(void *v) { return exponent(mig(cast(sz,v))); }	\
  static int mag_exp_##sz(void *v) { return exponent(norm(cast(sz,v))); }	\
  interval_float_description interval_float##sz##_desc =	\
    { { create: &create_##sz, destroy: &destroy_##sz, clone: &clone_##sz,	\
        add: &add_##sz, sub: &sub_##sz, mul: &mul_##sz, div: &div_##sz,		\
        subset: &subset_##sz, singleton: &singleton_##sz, in_zero: &zero_##sz,	\
        to_real: &real_##sz, hull: &hull_##sz, split: split_##sz, output: &output_##sz },	\
      mig_exp: &mig_exp_##sz, mag_exp: &mag_exp_##sz, prec: _prec, min_exp: _min,	\
      format_size: _fmt_sz };	\
  interval_description *interval_float##sz = &interval_float##sz##_desc.desc;

INTERVAL_FLOAT(32, 23, -126, 32)
INTERVAL_FLOAT(64, 52, -1022, 64)
INTERVAL_FLOAT(x80, 63, -16382, 80)
INTERVAL_FLOAT(128, 112, -16382, 128)

#define fdesc(p) reinterpret_cast< interval_float_description const * >(p)

int mig_exponent(interval const &v) { return (*fdesc(v.desc)->mig_exp)(v.ptr); }
int mag_exponent(interval const &v) { return (*fdesc(v.desc)->mag_exp)(v.ptr); }
int ulp_exponent(interval const &v) { return mag_exponent(v) - fdesc(v.desc)->prec; }
