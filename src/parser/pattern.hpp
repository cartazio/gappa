#ifndef PROOFS_PATTERN_HPP
#define PROOFS_PATTERN_HPP

#include <string>
#include <vector>
#include "parser/ast_real.hpp"

bool match(ast_real const *src, ast_real const *dst, ast_real_vect &);
ast_real const *rewrite(ast_real const *, ast_real_vect const &);

function_class const *absolute_rounding_error(ast_real const *, ast_real const *[2]);
function_class const *relative_rounding_error(ast_real const *, ast_real const *[2]);

enum condition_type { COND_LT, COND_LE, COND_GT, COND_GE, COND_NE, COND_NZ };

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

struct rewriting_rule;
typedef std::vector< pattern_cond > pattern_cond_vect;
typedef std::pair< ast_real const *, ast_real const * > pattern_excl;
typedef std::vector< pattern_excl > pattern_excl_vect;
typedef std::vector< rewriting_rule const * > rewriting_vect;

extern rewriting_vect rewriting_rules;

struct rewriting_rule {
  pattern src, dst;
  std::string name;
  pattern_cond_vect cond;
  pattern_excl_vect excl;
  rewriting_rule(pattern const &p1, pattern const &p2, std::string const &n,
                 pattern_cond_vect const &c, pattern_excl_vect const &e)
    : src(p1), dst(p2), name(n), cond(c), excl(e) {
    rewriting_rules.push_back(this);
  }
};

#endif // PROOFS_PATTERN_HPP
