#ifndef PARSER_PATTERN_HPP
#define PARSER_PATTERN_HPP

#include "parser/ast_real.hpp"
#include "proofs/property.hpp"

bool match(ast_real const *src, ast_real const *dst, ast_real_vect &);
ast_real const *rewrite(ast_real const *, ast_real_vect const &);

function_class const *absolute_rounding_error(ast_real const *, ast_real const *[2]);
function_class const *relative_rounding_error(predicated_real const &);

struct pattern_cond {
  ast_real const *real;
  condition_type type;
  int value;
};

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
  pattern_cond operator<(int) const;
  pattern_cond operator>(int) const;
  pattern_cond operator<=(int) const;
  pattern_cond operator>=(int) const;
  pattern_cond operator!=(int) const;
  pattern_cond operator~() const;
  static pattern abs(pattern const &);
  static pattern sqrt(pattern const &);
};

#endif // PARSER_PATTERN_HPP
