#ifndef PROOFS_PATTERN_HPP
#define PROOFS_PATTERN_HPP

#include "parser/ast_real.hpp"

typedef std::vector< rounding_class const * > rounding_vect;
bool match(ast_real const *src, ast_real const *dst, ast_real_vect &, rounding_vect &);
ast_real const *rewrite(ast_real const *, ast_real_vect const &, rounding_vect const &);

class pattern {
  ast_real const *real;
 public:
  operator ast_real const *() const { return real; }
  pattern(ast_real const &r): real(normalize(r)) {}
  pattern operator-() const;
  pattern operator+(pattern const &) const;
  pattern operator-(pattern const &) const;
  pattern operator*(pattern const &) const;
  pattern operator/(pattern const &) const;
  static pattern round(pattern const &, rounding_class const * = NULL);
};

#endif // PROOFS_PATTERN_HPP
