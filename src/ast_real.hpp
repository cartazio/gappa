#ifndef AST_REAL_HPP
#define AST_REAL_HPP

#include <boost/variant.hpp>
#include <vector>

struct variable;

struct ast_number {
  std::string mantissa;
  int exponent;
  int base;
};

enum real_op_type { UOP_MINUS, BOP_ADD, BOP_SUB, BOP_MUL, BOP_DIV };

struct real_op;

typedef boost::variant
  < ast_number *
  , variable *
  , boost::recursive_wrapper< real_op >
  > ast_real;

typedef std::vector< ast_real > ast_real_vect;

struct real_op
{
  ast_real_vect ops;
  real_op_type type;
  real_op(real_op_type t, ast_real_vect const &o): ops(o), type(t) {}
  real_op(real_op_type t, ast_real const &o): type(t) { ops.push_back(o); }
  real_op(ast_real const &l, real_op_type t, ast_real const &r): type(t) { ops.push_back(l); ops.push_back(r); }
  bool operator==(real_op const &v) const { return type == v.type && ops == v.ops; }
};

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream, real_op const &value)
{
  stream << "(" << value.type << /*' ' << value.left << ')'*/" ...)"; // TODO
  return stream;
}

#endif // AST_REAL_HPP
