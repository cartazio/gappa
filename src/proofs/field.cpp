#include "parser/pattern.hpp"

rewriting_vect rewriting_rules;

pattern_cond_vect operator&&(pattern_cond_vect const &v, pattern_cond const &c) {
  pattern_cond_vect res(v);
  res.push_back(c);
  return res;
}

pattern_excl operator^(pattern const &a, pattern const &b) {
  return pattern_excl(a, b);
}

pattern_excl_vect operator&&(pattern_excl_vect const &v, pattern_excl const &c) {
  pattern_excl_vect res(v);
  res.push_back(c);
  return res;
}

static pattern a(0), b(1), c(2), d(3), a_b(-1);

#define abs pattern::abs
#define sqrt pattern::sqrt

#define REWRITE(name,lhs,rhs) \
  static rewriting_rule rewriting_rule_##name \
  (lhs, rhs, #name, pattern_cond_vect(), pattern_excl_vect())
#define REWRIT3(name,lhs,rhs,cond) \
  static rewriting_rule rewriting_rule_##name \
  (lhs, rhs, #name, pattern_cond_vect() && cond, pattern_excl_vect())
#define REWRITe(name,lhs,rhs,excl) \
  static rewriting_rule rewriting_rule_##name \
  (lhs, rhs, #name, pattern_cond_vect(), pattern_excl_vect() && excl)
#define REWRIT9(name,lhs,rhs,cond,excl) \
  static rewriting_rule rewriting_rule_##name \
  (lhs, rhs, #name, pattern_cond_vect() && cond, pattern_excl_vect() && excl)

REWRITE(add_decomposition_rounded_left,
	b + c,
	(b - a) + (a + c));

REWRITE(add_decomposition_rounded_right,
	c + b,
	(c + a) + (b - a));

REWRITe(sub_decomposition_rounded_left,
	b - c,
	(b - a) + (a - c),
	a ^ c);

REWRITE(sub_decomposition_rounded_right,
	c - b,
	(c - a) + -(b - a));

REWRITE(mul_decomposition_rounded_left,
	b * c,
	(b - a) * c + a * c);

REWRITE(mul_decomposition_rounded_right,
	c * b,
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
	(b - c) / c,
	(b - a) / a + (a - c) / c + ((b - a) / a) * ((a - c) / c),
	~c && ~a,
	a ^ c);

REWRIT9(relative_to_absolute,
	a - b,
	((a - b) / b) * b,
	~b,
	a ^ b);

REWRIT9(mul_rel_decomposition,
	(a * b - c * d) / (c * d),
	(a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d),
	~c && ~d,
	a ^ c && b ^ d);

REWRIT9(mul_rel_decomposition_left,
	(a * b - a * c) / (a * c),
	(b - c) / c,
	~a && ~c,
	b ^ c);

REWRIT9(mul_rel_decomposition_right,
	(a * b - c * b) / (c * b),
	(a - c) / c,
	~b && ~c,
	a ^ c);

REWRIT3(square_sqrt,
	sqrt(a) * sqrt(a),
	a,
	a >= 0);

REWRITE(approx_to_accura_abs,
	b,
	a + (b - a));

REWRITE(accura_to_approx_abs,
        a_b,
        b + -(b - a));
