#include "parser/pattern.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/schemes.hpp"

struct pattern_factory: scheme_factory {
  pattern p1, p2;
  std::string name;
  pattern_factory(pattern const &q1, pattern const &q2, std::string const &n): p1(q1), p2(q2), name(n) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *pattern_factory::operator()(ast_real const *r) const {
  ast_real_vect holders;
  rounding_vect roundings;
  if (!match(r, p1, holders, roundings)) return NULL;
  return new rewrite_scheme(rewrite(p2, holders, roundings), name);
}

struct pattern_register {
  pattern_register(pattern const &p1, pattern const &p2, std::string const &n);
};

pattern_register::pattern_register(pattern const &p1, pattern const &p2, std::string const &n) {
  scheme_register dummy(new pattern_factory(p1, p2, n));
}

static pattern rnd(pattern const &a, int b) {
  return pattern(rounding_placeholder(a, b));
}

static pattern a(0), b(1), c(2), d(3);

#define REWRITE(name,lhs,rhs) static pattern_register name(lhs, rhs, #name)

REWRITE(absolute_error_sym,
	a - rnd(a, 0),
	-(rnd(a, 0) - a));

REWRITE(absolute_error_trans,
	rnd(a, 0) - b,
	(rnd(a, 0) - a) + (a - b));

REWRITE(add_decomposition,
	(a + b) - (c + d),
	(a - c) + (b - d));

REWRITE(sub_decomposition,
	(a - b) - (c - d),
	(a - c) - (b - d));

REWRITE(mul_decomposition_simple,
	a * b - c * d,
	a * (b - d) + d * (a - c));

REWRITE(mul_decomposition_full_left,
	a * b - c * d,
	a * (b - d) + b * (a - c) - (a - c) * (b - d));

REWRITE(mul_decomposition_full_right,
	a * b - c * d,
	c * (b - d) + d * (a - c) + (a - c) * (b - d));

REWRITE(relative_error_trans,
	(rnd(a, 0) - b) / b,
	((rnd(a, 0) - a) / a) + ((a - b) / b) + ((rnd(a, 0) - a) / a) * ((a - b) / b));

REWRITE(relative_to_absolute,
	a - b,
	((a - b) / b) * b);

REWRITE(mul_rel_decomposition,
	(a * b - c * d) / (c * d),
	(a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d));
