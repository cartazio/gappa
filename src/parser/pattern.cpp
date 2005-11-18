#include <set>
#include <boost/variant.hpp>
#include "parser/pattern.hpp"

ast_real const *morph(ast_real const *r, function_class const **f) {
  real_op const *p = boost::get < real_op const >(r);
  if (!p || !p->fun || p->fun->type == ROP_UNK) return NULL;
  if (f) *f = p->fun;
  if (p->fun->type == UOP_ID) return p->ops[0];
  return normalize(ast_real(real_op(p->fun->type, p->ops)));
}

struct match_visitor: boost::static_visitor< bool > {
  bool visit(ast_real const *src, ast_real const *dst) const;
  template< typename T, typename U > bool operator()(T const &, U const &) const { return false; }
  template< typename T > bool operator()(T const &r1, T const &r2) const { return r1 == r2; }
  bool operator()(real_op const &r1, real_op const &r2) const;
  ast_real_vect &holders;
  match_visitor(ast_real_vect &h): holders(h) {}
};

bool match_visitor::operator()(real_op const &r1, real_op const &r2) const {
  if (r1.type != r2.type || r1.fun != r2.fun) return false;
  unsigned s = r1.ops.size();
  if (s != r2.ops.size()) return false;
  for(unsigned i = 0; i < s; ++i)
    if (!visit(r1.ops[i], r2.ops[i])) return false;
  return true;
}

bool match_visitor::visit(ast_real const *src, ast_real const *dst) const {
  if (src == dst) return true;
  if (placeholder const *p = boost::get< placeholder const >(dst)) {
    int i = *p;
    if (i < -16) return true;
    unsigned j = (i < 0) ? 1 - i : 1 + i;
    if (j > holders.size())
      holders.resize(j, NULL);
    ast_real const *&r1 = holders[j - 1];
    if (!r1) r1 = src;
    else if (r1 != src) return false;
    if (i >= 0) return true;
    ast_real const *src2 = morph(src);
    if (!src2) return false;
    ast_real const *&r2 = holders[j - 2];
    if (!r2) r2 = src2;
    else if (r2 != src2) return false;
    return true;
  }
  return boost::apply_visitor(*this, *src, *dst);
}

bool match(ast_real const *src, ast_real const *dst, ast_real_vect &holders) {
  return match_visitor(holders).visit(src, dst);
}

struct rewrite_visitor: boost::static_visitor< ast_real const * > {
  ast_real const *visit(ast_real const *dst) const;
  template< typename T > ast_real const *operator()(T const &r) const { return normalize(ast_real(r)); }
  ast_real const *operator()(undefined_real const &) const { assert(false); }
  ast_real const *operator()(real_op const &r) const;
  ast_real const *operator()(placeholder i) const;
  ast_real_vect const &holders;
  rewrite_visitor(ast_real_vect const &h): holders(h) {}
};

ast_real const *rewrite_visitor::operator()(placeholder i) const {
  assert(unsigned(i) < holders.size() && holders[i]);
  return holders[i];
}

ast_real const *rewrite_visitor::operator()(real_op const &r) const {
  ast_real_vect ops;
  unsigned s = r.ops.size();
  ops.reserve(s);
  for(unsigned i = 0; i < s; ++i)
    ops.push_back(visit(r.ops[i]));
  return normalize(ast_real(real_op(r.type, r.fun, ops)));
}

ast_real const *rewrite_visitor::visit(ast_real const *dst) const {
  if (boost::get< undefined_real const >(dst)) return dst;
  return boost::apply_visitor(*this, *dst);
}

ast_real const *rewrite(ast_real const *dst, ast_real_vect const &holders) {
  return rewrite_visitor(holders).visit(dst);
}

typedef std::set< ast_real const * > real_set;

struct unknown_visitor: boost::static_visitor< void > {
  void visit(ast_real const *) const;
  template< typename T > void operator()(T const &) const { return; }
  void operator()(real_op const &) const;
  real_set &reals;
  unknown_visitor(real_set &r): reals(r) {}
};

void unknown_visitor::operator()(real_op const &r) const {
  for(ast_real_vect::const_iterator i = r.ops.begin(), end = r.ops.end(); i != end; ++i)
    visit(*i);
}

void unknown_visitor::visit(ast_real const *dst) const {
  if (boost::get< undefined_real const >(dst)) reals.insert(dst);
  return boost::apply_visitor(*this, *dst);
}

void find_unknown_reals(real_set &s, ast_real const *r) {
  unknown_visitor(s).visit(r);
}

#define PATTERN_OP(symb, op) \
  pattern pattern::operator symb(pattern const &p) const \
  { return pattern(real_op(real, BOP_##op, p.real)); }
PATTERN_OP(+, ADD)
PATTERN_OP(-, SUB)
PATTERN_OP(*, MUL)
PATTERN_OP(/, DIV)

#define PATTERN_COND(symb, op)	\
  pattern_cond pattern::operator symb(int v) const { \
    pattern_cond res;		\
    res.real = real;		\
    res.value = v;		\
    res.type = COND_##op;	\
    return res;			\
  }
PATTERN_COND(<, LT)
PATTERN_COND(>, GT)
PATTERN_COND(<=, LE)
PATTERN_COND(>=, GE)
PATTERN_COND(!=, NE)

pattern pattern::operator-() const {
  return pattern(real_op(UOP_NEG, real));
}

pattern pattern::abs(pattern const &p) {
  return pattern(real_op(UOP_ABS, p.real));
}
