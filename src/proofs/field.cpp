#include "parser/pattern.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/schemes.hpp"
#include <boost/preprocessor/cat.hpp>

struct pattern_factory: scheme_factory {
  pattern lhs, rhs;
  std::string name;
  pattern_cond_vect cond;
  pattern_factory(pattern const &q1, pattern const &q2, std::string const &n, pattern_cond_vect const &c)
  	: lhs(q1), rhs(q2), name(n), cond(c) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *pattern_factory::operator()(ast_real const *src) const {
  ast_real_vect holders;
  rounding_vect roundings;
  if (!match(src, lhs, holders, roundings)) return NULL;
  std::set< ast_real const * > hold(holders.begin(), holders.end());
  if (hold.size() != holders.size()) return NULL;
  ast_real const *dst = rewrite(rhs, holders, roundings);
  pattern_cond_vect c(cond);
  rewrite(c, holders, roundings);
  return new rewrite_scheme(src, dst, name, c);
}

struct pattern_register {
  pattern_register(pattern const &, pattern const &, std::string const &n, pattern_cond_vect const &c);
};

pattern_register::pattern_register(pattern const &p1, pattern const &p2,
                                   std::string const &n, pattern_cond_vect const &c) {
  scheme_register dummy(new pattern_factory(p1, p2, n, c));
}

static pattern rnd(pattern const &a, int b) {
  return pattern(rounding_placeholder(a, b));
}

static pattern a(0), b(1), c(2), d(3);

#define REWRITE_NAME BOOST_PP_CAT(rewrite_, __LINE__)
#define REWRITE(name,lhs,rhs) static pattern_register REWRITE_NAME(lhs, rhs, #name, pattern_cond_vect())
#define REWRIT3(name,lhs,rhs,cond) static pattern_register REWRITE_NAME(lhs, rhs, #name, pattern_cond_vect() && cond)

REWRITE(add_decomposition_rounded_left,
	rnd(a, 0) + b,
	(rnd(a, 0) - a) + (a + b));

REWRITE(add_decomposition_rounded_right,
	a + rnd(b, 0),
	(a + b) + (rnd(b, 0) - b));

REWRITE(sub_decomposition_rounded_left,
	rnd(a, 0) - b,
	(rnd(a, 0) - a) + (a - b));

REWRITE(sub_decomposition_rounded_right,
	a - rnd(b, 0),
	(a - b) + -(rnd(b, 0) - b));

REWRITE(mul_decomposition_rounded_left,
	rnd(a, 0) * b,
	(rnd(a, 0) - a) * b + a * b);

REWRITE(mul_decomposition_rounded_right,
	a * rnd(b, 0),
	a * (rnd(b, 0) - b) + a * b);

REWRITE(add_decomposition,
	(a + b) - (c + d),
	(a - c) + (b - d));

REWRITE(add_decomposition_left,
	(a + b) - (a + c),
	b - c);

REWRITE(add_decomposition_right,
	(a + b) - (c + b),
	a - c);

REWRITE(sub_decomposition,
	(a - b) - (c - d),
	(a - c) + -(b - d));

REWRITE(sub_decomposition_left,
	(a - b) - (a - c),
	-(b - c));

REWRITE(sub_decomposition_right,
	(a - b) - (c - b),
	a - c);

REWRITE(mul_decomposition_factor_left,
	a * b - a * c,
	a * (b - c));

REWRITE(mul_decomposition_factor_right,
	a * c - b * c,
	(a - b) * c);

REWRITE(mul_decomposition_half_left,
	a * b - c * d,
	a * (b - d) + (a - c) * d);

REWRITE(mul_decomposition_half_right,
	a * b - c * d,
	(a - c) * b + c * (b - d));

REWRITE(mul_decomposition_full_left,
	a * b - c * d,
	a * (b - d) + (a - c) * b + -((a - c) * (b - d)));

REWRITE(mul_decomposition_full_right,
	a * b - c * d,
	c * (b - d) + (a - c) * d + (a - c) * (b - d));

REWRIT3(relative_transitivity, //relative_error_trans,
	(rnd(a, 0) - b) / b,
	(rnd(a, 0) - a) / a + (a - b) / b + ((rnd(a, 0) - a) / a) * ((a - b) / b),
	b != 0 && a != 0);

REWRIT3(relative_to_absolute,
	a - b,
	((a - b) / b) * b,
	b != 0);

REWRIT3(mul_rel_decomposition,
	(a * b - c * d) / (c * d),
	(a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d),
	c != 0 && d != 0);

REWRIT3(mul_rel_decomposition_left,
	(a * b - a * c) / (a * c),
	(b - c) / c,
	a != 0 && c != 0);

REWRIT3(mul_rel_decomposition_right,
	(a * b - c * b) / (c * b),
	(a - c) / c,
	b != 0 && c != 0);
