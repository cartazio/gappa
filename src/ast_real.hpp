#ifndef AST_REAL_HPP
#define AST_REAL_HPP

#include <boost/variant.hpp>
#include <vector>

struct variable;

struct ast_number {
  std::string mantissa;
  int exponent;
  int base;
  bool operator<(ast_number const &v) const
  { return base < v.base || (base == v.base && (exponent < v.exponent || (exponent == v.exponent && mantissa < v.mantissa))); }
};

ast_number *normalize(ast_number const &);

struct ast_real;

enum real_op_type { UOP_MINUS, BOP_ADD, BOP_SUB, BOP_MUL, BOP_DIV };

typedef std::vector< ast_real const * > ast_real_vect;

struct real_op
{
  ast_real_vect ops;
  real_op_type type;
  real_op(real_op_type t, ast_real_vect const &o): ops(o), type(t) {}
  real_op(real_op_type t, ast_real *o): type(t) { ops.push_back(o); }
  real_op(ast_real *l, real_op_type t, ast_real *r): type(t) { ops.push_back(l); ops.push_back(r); }
  bool operator==(real_op const &v) const { return type == v.type && ops == v.ops; }
  bool operator<(real_op const &v) const { return type < v.type || (type == v.type && ops < v.ops); }
};

enum error_type { ERROR_ABS, ERROR_REL };

struct error_bound
{
  error_type type;
  variable *var;
  ast_real const *real;
  error_bound(error_type t, variable *v, ast_real const *r): type(t), var(v), real(r) {}
  bool operator==(error_bound const &v) const { return type == v.type && var == v.var && real == v.real; }
  bool operator<(error_bound const &v) const
  { return type < v.type || (type == v.type && (var < v.var || (var == v.var && real < v.real))); }
};

typedef boost::variant
  < ast_number *
  , variable *
  , real_op
  , error_bound
  > ast_real_aux;

struct proof_scheme;

struct ast_real: ast_real_aux
{
  proof_scheme const *scheme;
  ast_real(ast_number *v): ast_real_aux(v), scheme(NULL) {}
  ast_real(variable *v): ast_real_aux(v), scheme(NULL) {}
  ast_real(real_op const &v): ast_real_aux(v), scheme(NULL) {}
  ast_real(error_bound const &v): ast_real_aux(v), scheme(NULL) {}
  bool operator==(ast_real const &v) const { return ast_real_aux::operator==(static_cast< ast_real_aux const & >(v)); }
  bool operator<(ast_real const &v) const { return ast_real_aux::operator<(static_cast< ast_real_aux const & >(v)); }
  variable *get_variable() const { variable *const *v = boost::get< variable * const >(this); return v ? *v : NULL; }
};

ast_real *normalize(ast_real const &);

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream, real_op const &value)
{
  stream << "(" << value.type << /*' ' << value.left << ')'*/" ...)"; // TODO
  return stream;
}

struct ast_ident;

struct real_variable {
  ast_ident *name;
  ast_real *real;
  real_variable(ast_ident *n, ast_real *r): name(n), real(r) {}
};

#endif // AST_REAL_HPP
