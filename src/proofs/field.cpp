#include "parser/pattern.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/schemes.hpp"
#include <boost/preprocessor/cat.hpp>

struct pattern_factory: scheme_factory {
  pattern lhs, rhs, rew;
  std::string name;
  pattern_factory(pattern const &q1, pattern const &q2, pattern const &q3, std::string const &n)
  	: lhs(q1), rhs(q2), rew(q3), name(n) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *pattern_factory::operator()(ast_real const *src) const {
  ast_real_vect holders;
  rounding_vect roundings;
  if (!match(src, lhs, holders, roundings)) return NULL;
  ast_real const *dst = rewrite(rhs, holders, roundings);
  holders.clear();
  roundings.clear();
  bool b = match(dst, rew, holders, roundings);
  assert(b);
  return new rewrite_scheme(src, dst, name, holders);
}

struct pattern_register {
  pattern_register(pattern const &, pattern const &, std::string const &n, pattern const &);
};

pattern_register::pattern_register(pattern const &p1, pattern const &p2, std::string const &n, pattern const &p3) {
  scheme_register dummy(new pattern_factory(p1, p2, p3, n));
}

static pattern rnd(pattern const &a, int b) {
  return pattern(rounding_placeholder(a, b));
}

static pattern a(0), b(1), c(2), d(3);

#define REWRITE_NAME BOOST_PP_CAT(rewrite_, __LINE__)
#define REWRITE(name,lhs,rhs) static pattern_register REWRITE_NAME(lhs, rhs, #name, rhs)
#define REWRIT3(name,lhs,rhs,rew) static pattern_register REWRITE_NAME(lhs, rhs, #name, rew)

/*
REWRIT3(neg_sub, //absolute_error_sym,
	a - rnd(a, 0),
	-(rnd(a, 0) - a),
	-(b - a));

REWRIT3(absolute_transitivity, //absolute_error_trans,
	rnd(a, 0) - b,
	(rnd(a, 0) - a) + (a - b),
	(a - c) + (c - b));
*/

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
	(a - b) - (rnd(b, 0) - b));

REWRITE(mul_decomposition_rounded_left,
	rnd(a, 0) * b,
	(rnd(a, 0) - a) * b + a * b);

REWRITE(mul_decomposition_rounded_right,
	a * rnd(b, 0),
	a * (rnd(b, 0) - b) + a * b);

REWRITE(add_decomposition,
	(a + b) - (c + d),
	(a - c) + (b - d));

REWRITE(sub_decomposition,
	(a - b) - (c - d),
	(a - c) - (b - d));

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
	(a - c) / c + (c - b) / b + ((a - c) / c) * ((c - b) / b));

REWRITE(relative_to_absolute,
	a - b,
	((a - b) / b) * b);

REWRITE(mul_rel_decomposition,
	(a * b - c * d) / (c * d),
	(a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d));
