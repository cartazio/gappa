#ifndef PROOFS_PATTERN_HPP
#define PROOFS_PATTERN_HPP

#include "parser/ast_real.hpp"

bool match(ast_real const *src, ast_real const *dst, ast_real_vect &);
ast_real const *rewrite(ast_real const *, ast_real_vect const &);

enum condition_type { COND_LT, COND_LE, COND_GT, COND_GE, COND_NE };

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
  static pattern abs(pattern const &);
};

typedef std::vector< pattern_cond > pattern_cond_vect;

ast_real const *morph(ast_real const *, function_class const ** = NULL);

#endif // PROOFS_PATTERN_HPP
