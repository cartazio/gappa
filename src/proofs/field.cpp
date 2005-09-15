#include <boost/preprocessor/cat.hpp>
#include "parser/pattern.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/schemes.hpp"

pattern_cond_vect operator&&(pattern_cond_vect const &v, pattern_cond const &c) {
  pattern_cond_vect res(v);
  res.push_back(c);
  return res;
}

typedef std::pair< ast_real const *, ast_real const * > pattern_excl;
typedef std::vector< pattern_excl > pattern_excl_vect;

pattern_excl operator^(pattern const &a, pattern const &b) {
  return pattern_excl(a, b);
}

pattern_excl_vect operator&&(pattern_excl_vect const &v, pattern_excl const &c) {
  pattern_excl_vect res(v);
  res.push_back(c);
  return res;
}

struct pattern_factory: scheme_factory {
  pattern lhs, rhs;
  std::string name;
  pattern_cond_vect cond;
  pattern_excl_vect excl;
  pattern_factory(pattern const &q1, pattern const &q2, std::string const &n,
                  pattern_cond_vect const &c, pattern_excl_vect const &e)
    : lhs(q1), rhs(q2), name(n), cond(c), excl(e) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *pattern_factory::operator()(ast_real const *src) const {
  ast_real_vect holders;
  if (!match(src, lhs, holders)) return NULL;
  std::set< ast_real const * > hold(holders.begin(), holders.end());
  ast_real const *dst = rewrite(rhs, holders);
  for(pattern_excl_vect::const_iterator i = excl.begin(), end = excl.end(); i != end; ++i)
    if (rewrite(i->first, holders) == rewrite(i->second, holders))
      return NULL;
  pattern_cond_vect c(cond);
  for(pattern_cond_vect::iterator i = c.begin(), end = c.end(); i != end; ++i)
    i->real = rewrite(i->real, holders);
  return new rewrite_scheme(src, dst, name, c);
}

struct pattern_register {
  pattern_register(pattern const &, pattern const &, std::string const &,
                   pattern_cond_vect const &, pattern_excl_vect const &);
};

pattern_register::pattern_register(pattern const &p1, pattern const &p2, std::string const &n,
                                   pattern_cond_vect const &c, pattern_excl_vect const &e) {
  scheme_register dummy(new pattern_factory(p1, p2, n, c, e));
}

static pattern a(0), b(1), c(2), d(3), b_a(-1);

// exported patterns
pattern absolute_error_pattern(b_a - a), relative_error_pattern((b_a - a) / a);

#define abs pattern::abs

#define REWRITE_NAME BOOST_PP_CAT(rewrite_, __LINE__)
#define REWRITE(name,lhs,rhs) \
  static pattern_register REWRITE_NAME \
  (lhs, rhs, #name, pattern_cond_vect(), pattern_excl_vect())
#define REWRIT3(name,lhs,rhs,cond) \
  static pattern_register REWRITE_NAME \
  (lhs, rhs, #name, pattern_cond_vect() && cond, pattern_excl_vect())
#define REWRITe(name,lhs,rhs,excl) \
  static pattern_register REWRITE_NAME \
  (lhs, rhs, #name, pattern_cond_vect(), pattern_excl_vect() && excl)
#define REWRIT9(name,lhs,rhs,cond,excl) \
  static pattern_register REWRITE_NAME \
  (lhs, rhs, #name, pattern_cond_vect() && cond, pattern_excl_vect() && excl)

REWRITE(add_decomposition_rounded_left,
	b_a + c,
	(b - a) + (a + c));

REWRITE(add_decomposition_rounded_right,
	c + b_a,
	(c + a) + (b - a));

REWRITe(sub_decomposition_rounded_left,
	b_a - c,
	(b - a) + (a - c),
	a ^ c);

REWRITE(sub_decomposition_rounded_right,
	c - b_a,
	(c - a) + -(b - a));

REWRITE(mul_decomposition_rounded_left,
	b_a * c,
	(b - a) * c + a * c);

REWRITE(mul_decomposition_rounded_right,
	c * b_a,
	c * (b - a) + c * a);

REWRITe(add_decomposition,
	(a + b) - (c + d),
	(a - c) + (b - d),
	a ^ c && b ^ d);

REWRITe(add_decomposition_left,
	(a + b) - (a + c),
	b - c,
	b ^ c);

REWRITe(add_decomposition_right,
	(a + b) - (c + b),
	a - c,
	a ^ c);

REWRITe(sub_decomposition,
	(a - b) - (c - d),
	(a - c) + -(b - d),
	a ^ c && b ^ d);

REWRITe(sub_decomposition_left,
	(a - b) - (a - c),
	-(b - c),
	b ^ c);

REWRITe(sub_decomposition_right,
	(a - b) - (c - b),
	a - c,
	a ^ c);

REWRITe(mul_decomposition_factor_left,
	a * b - a * c,
	a * (b - c),
	b ^ c);

REWRITe(mul_decomposition_factor_right,
	a * c - b * c,
	(a - b) * c,
	a ^ b);

REWRITe(mul_decomposition_half_left,
	a * b - c * d,
	a * (b - d) + (a - c) * d,
	a ^ c && b ^ d);

REWRITe(mul_decomposition_half_right,
	a * b - c * d,
	(a - c) * b + c * (b - d),
	a ^ c && b ^ d);

REWRITe(mul_decomposition_full_left,
	a * b - c * d,
	a * (b - d) + (a - c) * b + -((a - c) * (b - d)),
	a ^ c && b ^ d);

REWRITe(mul_decomposition_full_right,
	a * b - c * d,
	c * (b - d) + (a - c) * d + (a - c) * (b - d),
	a ^ c && b ^ d);

REWRIT9(relative_transitivity, //relative_error_trans,
	(b_a - c) / c,
	(b - a) / a + (a - c) / c + ((b - a) / a) * ((a - c) / c),
	abs(c) > 0 && abs(a) > 0,
	a ^ c);

REWRIT9(relative_to_absolute,
	a - b,
	((a - b) / b) * b,
	abs(b) > 0,
	a ^ b);

REWRIT9(mul_rel_decomposition,
	(a * b - c * d) / (c * d),
	(a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d),
	abs(c) > 0 && abs(d) > 0,
	a ^ c && b ^ d);

REWRIT9(mul_rel_decomposition_left,
	(a * b - a * c) / (a * c),
	(b - c) / c,
	abs(a) > 0 && abs(c) > 0,
	b ^ c);

REWRIT9(mul_rel_decomposition_right,
	(a * b - c * b) / (c * b),
	(a - c) / c,
	abs(b) > 0 && abs(c) > 0,
	a ^ c);
