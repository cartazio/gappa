#include "parser/pattern.hpp"
#include <boost/variant.hpp>

struct match_visitor: boost::static_visitor< bool > {
  bool visit(ast_real const *src, ast_real const *dst) const;
  template< typename T, typename U > bool operator()(T const &, U const &) const { return false; }
  template< typename T > bool operator()(T const &r1, T const &r2) const { return r1 == r2; }
  bool operator()(real_op const &r1, real_op const &r2) const;
  bool operator()(rounded_real const &r1, rounded_real const &r2) const;
  bool operator()(rounded_real const &r1, rounding_placeholder const &r2) const;
  ast_real_vect &holders;
  rounding_vect &roundings;
  match_visitor(ast_real_vect &h, rounding_vect &r): holders(h), roundings(r) {}
};

bool match_visitor::operator()(real_op const &r1, real_op const &r2) const {
  if (r1.type != r2.type) return false;
  unsigned s = r1.ops.size();
  if (s != r2.ops.size()) return false;
  for(unsigned i = 0; i < s; ++i)
    if (!visit(r1.ops[i], r2.ops[i])) return false;
  return true;
}

bool match_visitor::operator()(rounded_real const &r1, rounded_real const &r2) const {
  return (!r2.rounding || r1.rounding == r2.rounding) && visit(r1.rounded, r2.rounded);
}

bool match_visitor::operator()(rounded_real const &r1, rounding_placeholder const &r2) const {
  int i = r2.holder;
  if (i >= 0) {
    if (unsigned(i + 1) >= roundings.size())
      roundings.resize(i + 1, NULL);
    rounding_class const *r = roundings[i];
    if (r) { if (r1.rounding != r) return false; }
    else roundings[i] = r1.rounding;
  }
  return visit(r1.rounded, r2.rounded);
}

bool match_visitor::visit(ast_real const *src, ast_real const *dst) const {
  if (placeholder const *p = boost::get< placeholder const >(dst)) {
    int i = *p;
    if (i >= 0) {
      if (unsigned(i + 1) >= holders.size())
        holders.resize(i + 1, NULL);
      ast_real const *r = holders[i];
      if (r) { if (src != r) return false; }
      else holders[i] = src;
    }
    return true;
  }
  return boost::apply_visitor(*this, *src, *dst);
}

bool match(ast_real const *src, ast_real const *dst, ast_real_vect &holders, rounding_vect &roundings) {
  return match_visitor(holders, roundings).visit(src, dst);
}

struct rewrite_visitor: boost::static_visitor< ast_real const * > {
  ast_real const *visit(ast_real const *dst) const { return boost::apply_visitor(*this, *dst); }
  template< typename T > ast_real const *operator()(T const &r) const { return normalize(ast_real(r)); }
  ast_real const *operator()(real_op const &r) const;
  ast_real const *operator()(rounded_real const &r) const;
  ast_real const *operator()(rounding_placeholder const &r) const;
  ast_real const *operator()(placeholder i) const;
  ast_real_vect const &holders;
  rounding_vect const &roundings;
  rewrite_visitor(ast_real_vect const &h, rounding_vect const &r): holders(h), roundings(r) {}
};

ast_real const *rewrite_visitor::operator()(placeholder i) const {
  assert(i >= 0 && unsigned(i) < holders.size() && holders[i]);
  return holders[i];
}

ast_real const *rewrite_visitor::operator()(real_op const &r) const {
  ast_real_vect ops;
  unsigned s = r.ops.size();
  ops.reserve(s);
  for(unsigned i = 0; i < s; ++i)
    ops.push_back(visit(r.ops[i]));
  return normalize(ast_real(real_op(r.type, ops)));
}

ast_real const *rewrite_visitor::operator()(rounded_real const &r) const {
  return normalize(ast_real(rounded_real(visit(r.rounded), r.rounding)));
}

ast_real const *rewrite_visitor::operator()(rounding_placeholder const &r) const {
  int i = r.holder;
  assert(i >= 0 && unsigned(i) < roundings.size() && roundings[i]);
  return normalize(ast_real(rounded_real(visit(r.rounded), roundings[i])));
}

ast_real const *rewrite(ast_real const *dst, ast_real_vect const &holders, rounding_vect const &roundings) {
  return rewrite_visitor(holders, roundings).visit(dst);
}

pattern pattern::operator-() const { return pattern(real_op(UOP_MINUS, real)); }
pattern pattern::operator+(pattern const &p) const { return pattern(real_op(real, BOP_ADD, p.real)); }
pattern pattern::operator-(pattern const &p) const { return pattern(real_op(real, BOP_SUB, p.real)); }
pattern pattern::operator*(pattern const &p) const { return pattern(real_op(real, BOP_MUL, p.real)); }
pattern pattern::operator/(pattern const &p) const { return pattern(real_op(real, BOP_DIV, p.real)); }

pattern pattern::round(pattern const &p, rounding_class const *r) {
  return pattern(rounded_real(p.real, r));
}
