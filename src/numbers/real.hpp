#ifndef NUMBERS_REAL_HPP
#define NUMBERS_REAL_HPP

#include <gmp.h>
#include <mpfr.h>

struct ref_counter_t {
  int nb;
  ref_counter_t(): nb(1) {}
  void incr() { ++nb; }
  bool decr() { return --nb == 0; }
};

struct number_base {
  static int const real_prec = 150;
  mutable ref_counter_t ref_counter;
  mpfr_t val;
  number_base() { mpfr_init2(val, real_prec); }
  ~number_base() { mpfr_clear(val); }
  number_base const *clone() const { ref_counter.incr(); return this; }
  void destroy() const { if (ref_counter.decr()) delete this; }
};

extern number_base *empty_mpfr;

struct number {
  mutable number_base const *data;
  mpfr_t const &mpfr_data() const { return data->val; }

  number(): data(empty_mpfr->clone()) {}
  number(int v);
  number(number_base const *d): data(d) {}
  number(number const &v): data(v.data->clone()) {}
  number &operator=(number const &v);
  ~number() { data->destroy(); }
  number_base *unique() const;
  bool operator<=(number const &v) const { return mpfr_lessequal_p(data->val, v.data->val); }
  bool operator>=(number const &v) const { return mpfr_greaterequal_p(data->val, v.data->val); }
  bool operator<(number const &v) const { return mpfr_less_p(data->val, v.data->val); }
  bool operator>(number const &v) const { return mpfr_greater_p(data->val, v.data->val); }
  bool operator==(number const &v) const { return mpfr_equal_p(data->val, v.data->val); }
  bool operator!=(number const &v) const { return mpfr_lessgreater_p(data->val, v.data->val); }
  number operator-() const;
  static number pos_inf, neg_inf;
};

number const &min(number const &x, number const &y);
number const &max(number const &x, number const &y);

namespace boost { namespace numeric { namespace interval_lib { namespace user {

inline bool is_zero(::number const &v) { return mpfr_sgn(v.data->val) == 0; }
inline bool is_neg(::number const &v)  { return mpfr_sgn(v.data->val) < 0; }
inline bool is_pos(::number const &v)  { return mpfr_sgn(v.data->val) > 0; }

} } } }

#endif // NUMBER_REAL_HPP
