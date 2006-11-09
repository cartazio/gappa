#include <boost/preprocessor/cat.hpp>
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

static pattern a(0), b(1), c(2), d(3), a_b(-1), one(token_one);

pattern add_relative_helper((c * a + d * b) / (a + b));

#define abs pattern::abs
#define sqrt pattern::sqrt

#define REWRITING_NAME BOOST_PP_CAT(rewriting_rule_,__LINE__)

#define REWRITE(name,lhs,rhs) \
  static rewriting_rule REWRITING_NAME \
  (lhs, rhs, #name, pattern_cond_vect(), pattern_excl_vect())
#define REWRIT3(name,lhs,rhs,cond) \
  static rewriting_rule REWRITING_NAME \
  (lhs, rhs, #name, pattern_cond_vect() && cond, pattern_excl_vect())
#define REWRITe(name,lhs,rhs,excl) \
  static rewriting_rule REWRITING_NAME \
  (lhs, rhs, #name, pattern_cond_vect(), pattern_excl_vect() && excl)
#define REWRIT9(name,lhs,rhs,cond,excl) \
  static rewriting_rule REWRITING_NAME \
  (lhs, rhs, #name, pattern_cond_vect() && cond, pattern_excl_vect() && excl)

/*
Naming convention: operator name followed by
  x (expand term)      f (factor term)      m (mix)
  a (approximate expr) e (accurate expr)    i (irrelevant)
  l (left hand side)   r (right hand side)  b (both)
  s (absolute error)   q (relative error)
*/

// OPP

REWRITe(opp_mibs,
	-a - -b,
	-(a - b),
	a ^ b);

REWRIT9(opp_mibs,
	(-a - -b) / -b,
	(a - b) / b,
	~b,
	a ^ b);

// ADD

REWRITE(add_xals,
	b + c,
	(b - a) + (a + c));

REWRITE(add_xars,
	c + b,
	(c + a) + (b - a));

REWRITe(add_mibs,
	(a + b) - (c + d),
	(a - c) + (b - d),
	a ^ c && b ^ d);

REWRIT3(add_mibq,
	((a + b) - (c + d)) / (c + d),
	((a - c) / c * c + (b - d) / d * d) / (c + d),
	~c && ~d && ~(c + d));

REWRITe(add_fils,
	(a + b) - (a + c),
	b - c,
	b ^ c);

REWRITe(add_firs,
	(a + b) - (c + b),
	a - c,
	a ^ c);

// SUB

REWRITe(sub_xals,
	b - c,
	(b - a) + (a - c),
	a ^ c && b ^ c);

REWRITe(sub_xars,
	c - b,
	(c - a) + -(b - a),
	b ^ c); // no a^c so that the rule can be used to revert a-b

REWRITe(sub_mibs,
	(a - b) - (c - d),
	(a - c) + -(b - d),
	a ^ c && b ^ d);

REWRIT3(sub_mibq,
	((a - b) - (c - d)) / (c - d),
	((a - c) / c * c + (b - d) / d * -d) / (c + -d),
	~c && ~d && ~(c - d));

REWRITe(sub_fils,
	(a - b) - (a - c),
	-(b - c),
	b ^ c);

REWRITe(sub_firs,
	(a - b) - (c - b),
	a - c,
	a ^ c);

// MUL

REWRITE(mul_xals,
	b * c,
	(b - a) * c + a * c);

REWRITE(mul_xars,
	c * b,
	c * (b - a) + c * a);

REWRITe(mul_fils,
	a * b - a * c,
	a * (b - c),
	b ^ c);

REWRITe(mul_firs,
	a * c - b * c,
	(a - b) * c,
	a ^ b);

REWRITe(mul_mars,
	a * b - c * d,
	a * (b - d) + (a - c) * d,
	a ^ c && b ^ d);

REWRITe(mul_mals,
	a * b - c * d,
	(a - c) * b + c * (b - d),
	a ^ c && b ^ d);

REWRITe(mul_mabs,
	a * b - c * d,
	a * (b - d) + (a - c) * b + -((a - c) * (b - d)),
	a ^ c && b ^ d);

REWRITe(mul_mibs,
	a * b - c * d,
	c * (b - d) + (a - c) * d + (a - c) * (b - d),
	a ^ c && b ^ d);

REWRIT9(mul_mibq,
	(a * b - c * d) / (c * d),
	(a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d),
	~c && ~d,
	a ^ c && b ^ d);

REWRIT9(mul_filq,
	(a * b - a * c) / (a * c),
	(b - c) / c,
	~a && ~c,
	b ^ c);

REWRIT9(mul_firq,
	(a * b - c * b) / (c * b),
	(a - c) / c,
	~b && ~c,
	a ^ c);

// DIV

REWRIT9(div_mibq,
	(a / b - c / d) / (c / d),
	((a - c) / c - (b - d) / d) / (one + (b - d) / d),
	~b && ~c && ~d,
	b ^ d);

REWRIT9(div_firq,
	(a / b - c / b) / (c / b),
	(a - c) / c,
	~b && ~c,
	a ^ c);

// SQRT

REWRIT9(sqrt_mibs,
	sqrt(a) - sqrt(b),
	(a - b) / (sqrt(a) + sqrt(b)),
	a >= 0 && b >= 0,
	a ^ b);

REWRIT9(sqrt_mibq,
	(sqrt(a) - sqrt(b)) / sqrt(b),
	sqrt(one + (a - b) / b) - one,
	a >= 0 && b > 0,
	a ^ b);

// ERR

REWRITe(sub_xals, //actually err_xers
	c - a,
	(c - b) + (b - a),
	a ^ c && b ^ c);

REWRIT9(err_xalq,
	(b - c) / c,
	(b - a) / a + (a - c) / c + ((b - a) / a) * ((a - c) / c),
	~c && ~a,
	a ^ c && b ^ c);

REWRIT9(err_xalq, //actually err_xerq
	(c - a) / a,
	(c - b) / b + (b - a) / a + ((c - b) / b) * ((b - a) / a),
	~a && ~b,
	a ^ c && b ^ c);

REWRIT9(err_xibq,
	a - b,
	((a - b) / b) * b,
	~b,
	a ^ b);

/* bad bad Zoot
REWRIT9(err_xabq,
	a / b,
	one + (a - b) / b,
	~b,
	a ^ b);
*/

REWRIT9(err_fabq,
	one + (a - b) / b,
	a / b,
	~b,
	a ^ b);

// VAL

REWRITE(val_xabs,
	b,
	a + (b - a));

REWRITE(val_xebs,
        a_b,
        b + -(b - a));

REWRIT3(val_xabq,
	b,
	a * (one + (b - a) / a),
	~a);

REWRIT3(val_xebq,
	a_b,
	b / (one + (b - a) / a),
	~a && ~b);

// BLI

REWRIT3(square_sqrt,
	sqrt(a) * sqrt(a),
	a,
	a >= 0);
