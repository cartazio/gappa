#ifndef AST_REAL_HPP
#define AST_REAL_HPP

#include <boost/variant.hpp>

struct variable;

struct ast_number {
  std::string mantissa;
  int exponent;
  int base;
};

enum real_unary_op { UOP_MINUS };
enum real_binary_op { BOP_ADD, BOP_SUB, BOP_MUL, BOP_DIV };

struct unary_op;
struct binary_op;

typedef boost::variant
  < ast_number *
  , variable *
  , boost::recursive_wrapper< unary_op >
  , boost::recursive_wrapper< binary_op >
  > ast_real;

struct unary_op
{
  ast_real left;
  real_unary_op type;
  unary_op(real_unary_op t, ast_real const &lhs): left(lhs), type(t) {}
  bool operator==(unary_op const &v) const { return type == v.type && left == v.left; }
};

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream, unary_op const &value)
{
  stream << "(U" << value.type << ' ' << value.left << ')';
  return stream;
}

struct binary_op
{
  ast_real left, right;
  real_binary_op type;
  binary_op(ast_real const &lhs, real_binary_op t, ast_real const &rhs): left(lhs), right(rhs), type(t) {}
  bool operator==(binary_op const &v) const { return type == v.type && left == v.left && right == v.right; }
};

template< class CharType, class CharTraits >
std::basic_ostream< CharType, CharTraits > &operator<<
  (std::basic_ostream< CharType, CharTraits > &stream, binary_op const &value)
{
  stream << "(B" << value.type << ' ' << value.left << ' ' << value.right << ')';
  return stream;
}

#endif // AST_REAL_HPP
