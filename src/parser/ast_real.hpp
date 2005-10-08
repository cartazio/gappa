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

enum real_op_type { UOP_ID, UOP_NEG, UOP_ABS, BOP_ADD, BOP_SUB, BOP_MUL, BOP_DIV, ROP_FUN, ROP_UNK };

struct interval;

struct function_class {
  real_op_type type;
  int theorem_mask;
  static const int TH_RND = 1, TH_ENF = 2, TH_ABS = 4, TH_ABS_REA = 8,
                   TH_ABS_RND = 16, TH_REL_REA = 32, TH_REL_RND = 64;
  function_class(real_op_type t, int m): type(t), theorem_mask(m) {}
  virtual interval round                      (interval const &, std::string &) const;
  virtual interval enforce                    (interval const &, std::string &) const;
  virtual interval absolute_error                               (std::string &) const;
  virtual interval absolute_error_from_real   (interval const &, std::string &) const;
  virtual interval absolute_error_from_rounded(interval const &, std::string &) const;
  virtual interval relative_error_from_real   (interval const &, std::string &) const;
  virtual interval relative_error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const = 0;
  virtual ~function_class() {}
};

struct ast_real;

typedef std::vector< ast_real const * > ast_real_vect;

struct real_op
{
  ast_real_vect ops;
  function_class const *fun;
  real_op_type type;
  real_op(real_op_type t, ast_real_vect const &o): ops(o), fun(NULL), type(t) {}
  real_op(real_op_type t, function_class const *f, ast_real_vect const &o): ops(o), fun(f), type(t) {}
  real_op(function_class const *f, ast_real_vect const &o): ops(o), fun(f), type(ROP_FUN) {}
  real_op(function_class const *f, ast_real const *o): ops(1, o), fun(f), type(ROP_FUN) {}
  real_op(real_op_type t, ast_real const *o): ops(1, o), fun(NULL), type(t) {}
  real_op(ast_real const *l, real_op_type t, ast_real const *r): fun(NULL), type(t) { ops.push_back(l); ops.push_back(r); }
  bool operator==(real_op const &v) const { return type == v.type && fun == v.fun && ops == v.ops; }
  bool operator<(real_op const &v) const
  { return type < v.type || (type == v.type && (fun < v.fun || (fun == v.fun && ops < v.ops))); }
};

struct ast_ident;

typedef int placeholder;

typedef boost::blank undefined_real;

typedef boost::variant
  < undefined_real
  , ast_number const *
  , real_op
  , placeholder
  > ast_real_aux;

struct ast_real: ast_real_aux
{
  mutable ast_ident const *name;
  ast_real(ast_ident const *v): ast_real_aux(undefined_real()), name(v) {}
  ast_real(ast_number const *v): ast_real_aux(v), name(NULL) {}
  ast_real(real_op const &v): ast_real_aux(v), name(NULL) {}
  ast_real(placeholder v): ast_real_aux(v), name(NULL) {}
  bool operator==(ast_real const &v) const;
  bool operator<(ast_real const &v) const;
};

ast_real *normalize(ast_real const &);
bool match(ast_real const *, ast_real const *, ast_real_vect &);
ast_real const *rewrite(ast_real const *, ast_real_vect const &);

#endif // PARSER_AST_REAL_HPP
