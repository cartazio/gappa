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

pattern rounding_p(int a, int b) {
  return pattern(rounding_placeholder(pattern(a), b));
}

pattern_register absolute_error_trans(
  pattern(0) - rounding_p(1, 0),
  (pattern(0) - pattern(1)) + (pattern(1) - rounding_p(1, 0)),
  "absolute_error_trans");

/*
pattern_register add_decomposition(
  (pattern(0) + pattern(1)) - (rounding_p(2, 0) + rounding_p(3, 1)),
  (pattern(0) - rounding_p(2, 0)) + (pattern(1) - rounding_p(3, 1)),
  "add_decomposition");

pattern_register sub_decomposition(
  (pattern(0) - pattern(1)) - (rounding_p(2, 0) - rounding_p(3, 1)),
  (pattern(0) - rounding_p(2, 0)) - (pattern(1) - rounding_p(3, 1)),
  "sub_decomposition");
*/

pattern_register add_decomposition(
  (pattern(0) + pattern(1)) - (pattern(2) + pattern(3)),
  (pattern(0) - pattern(2)) + (pattern(1) - pattern(3)),
  "add_decomposition");

pattern_register sub_decomposition(
  (pattern(0) - pattern(1)) - (pattern(2) - pattern(3)),
  (pattern(0) - pattern(2)) - (pattern(1) - pattern(3)),
  "sub_decomposition");

/*
pattern_register mul_decomposition(
  pattern(0) * pattern(1) - rounding_p(2, 0) * rounding_p(3, 1),
  pattern(0) * (pattern(1) - rounding_p(3, 1)) + rounding_p(3, 1) * (pattern(0) - rounding_p(2, 0)),
  "mul_decomposition");
*/

pattern_register mul_decomposition(
  pattern(0) * pattern(1) - rounding_p(2, 0) * rounding_p(3, 1),
  rounding_p(2, 0) * (pattern(1) - rounding_p(3, 1)) +
  rounding_p(3, 1) * (pattern(0) - rounding_p(2, 0)) +
  (pattern(0) - rounding_p(2, 0)) * (pattern(1) - rounding_p(3, 1)),
  "mul_decomposition");
