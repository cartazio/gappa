#ifndef PARSER_AST_REAL_HPP
#define PARSER_AST_REAL_HPP

#include <string>
#include <vector>
#include <boost/blank.hpp>
#include <boost/variant/get.hpp>
#include <boost/variant/recursive_wrapper.hpp>
#include <boost/variant/variant.hpp>

struct ast_number {
  std::string mantissa;
  int exponent;
  int base;
  bool operator<(ast_number const &v) const
  { return base < v.base || (base == v.base && (exponent < v.exponent || (exponent == v.exponent && mantissa < v.mantissa))); }
};

ast_number *normalize(ast_number const &);

struct ast_real;

enum real_op_type { UOP_MINUS, BOP_ADD, BOP_SUB, BOP_MUL, BOP_DIV, ROP_UNK };

typedef std::vector< ast_real const * > ast_real_vect;

struct real_op
{
  ast_real_vect ops;
  real_op_type type;
  real_op(real_op_type t, ast_real_vect const &o): ops(o), type(t) {}
  real_op(real_op_type t, ast_real const *o): type(t) { ops.push_back(o); }
  real_op(ast_real const *l, real_op_type t, ast_real const *r): type(t) { ops.push_back(l); ops.push_back(r); }
  bool operator==(real_op const &v) const { return type == v.type && ops == v.ops; }
  bool operator<(real_op const &v) const { return type < v.type || (type == v.type && ops < v.ops); }
};

struct rounding_class;

struct rounded_real
{
  ast_real const *rounded;
  rounding_class const *rounding;
  rounded_real(ast_real const *f, rounding_class const *r): rounded(f), rounding(r) {}
  bool operator==(rounded_real const &v) const { return rounded == v.rounded && rounding == v.rounding; }
  bool operator<(rounded_real const &v) const { return rounded < v.rounded || (rounded == v.rounded && rounding < v.rounding); }
};

struct ast_ident;

typedef int placeholder;

struct rounding_placeholder
{
  ast_real const *rounded;
  int holder;
  rounding_placeholder(ast_real const *f, int r): rounded(f), holder(r) {}
  bool operator==(rounding_placeholder const &v) const { return rounded == v.rounded && holder == v.holder; }
  bool operator<(rounding_placeholder const &v) const { return rounded < v.rounded || (rounded == v.rounded && holder < v.holder); }
};

typedef boost::blank undefined_real;

typedef boost::variant
  < undefined_real
  , ast_number const *
  , real_op
  , rounded_real
  , placeholder
  , rounding_placeholder
  > ast_real_aux;

struct proof_scheme;

struct ast_real: ast_real_aux
{
  mutable proof_scheme const *scheme;
  mutable ast_ident const *name;
  ast_real(ast_ident const *v): ast_real_aux(undefined_real()), scheme(NULL), name(v) {}
  ast_real(ast_number const *v): ast_real_aux(v), scheme(NULL), name(NULL) {}
  ast_real(real_op const &v): ast_real_aux(v), scheme(NULL), name(NULL) {}
  ast_real(rounded_real const &v): ast_real_aux(v), scheme(NULL), name(NULL) {}
  ast_real(placeholder v): ast_real_aux(v), scheme(NULL), name(NULL) {}
  ast_real(rounding_placeholder const &v): ast_real_aux(v), scheme(NULL), name(NULL) {}
  bool operator==(ast_real const &v) const;
  bool operator<(ast_real const &v) const;
};

ast_real *normalize(ast_real const &);
bool match(ast_real const *, ast_real const *, ast_real_vect &);
ast_real const *rewrite(ast_real const *, ast_real_vect const &);

#endif // PARSER_AST_REAL_HPP
