#include "parser/ast.hpp"

#include <cassert>
#include <iostream>
#include <map>
#include <sstream>

typedef std::map< ast_real const *, int > product;
typedef std::map< product, int > sum;

template< class T > std::map< T, int >
static weighted_union(std::map< T, int > const &m1, std::map< T, int > const &m2) {
  std::map< T, int > res;
  typename std::map< T, int >::const_iterator
  	i1 = m1.begin(), e1 = m1.end(),
  	i2 = m2.begin(), e2 = m2.end();
  while (i1 != e1 && i2 != e2) {
    if (i1->first < i2->first) res.insert(*i1++); else
    if (i2->first < i1->first) res.insert(*i2++); else
    {
      assert(i1->first == i2->first);
      int k = i1->second + i2->second;
      if (k != 0) res.insert(std::make_pair(i1->first, k));
      ++i1;
      ++i2;
    }
  }
  res.insert(i1, e1);
  res.insert(i2, e2);
  return res;
}

static product mul(product const &p1, product const &p2) {
  return weighted_union(p1, p2);
}

static sum neg(sum const &s) {
  sum res;
  for(sum::const_iterator i = s.begin(), end = s.end(); i != end; ++i)
    res.insert(std::make_pair(i->first, -i->second));
  return res;
}

static sum add(sum const &s1, sum const &s2) {
  return weighted_union(s1, s2);
}

static sum mul(sum const &s1, sum const &s2) {
  sum res;
  for(sum::const_iterator i = s1.begin(), i_end = s1.end(); i != i_end; ++i)
    for(sum::const_iterator j = s2.begin(), j_end = s2.end(); j != j_end; ++j) {
      sum tmp;
      tmp.insert(std::make_pair(mul(i->first, j->first), i->second * j->second));
      res = add(res, tmp);
    }
  return res;
}

static sum ringalize(ast_real const *r) {
  if (real_op const *o = boost::get< real_op const >(r))
    switch (o->type) {
    case UOP_MINUS:	return neg(ringalize(o->ops[0]));
    case BOP_ADD:	return add(ringalize(o->ops[0]), ringalize(o->ops[1]));
    case BOP_SUB:	return add(ringalize(o->ops[0]), neg(ringalize(o->ops[1])));
    case BOP_MUL:	return mul(ringalize(o->ops[0]), ringalize(o->ops[1]));
    default: ;
    }
  sum s;
  product p;
  if (ast_number const *const *n = boost::get< ast_number const *const >(r)) {
    if ((*n)->base == 0) return s;
    if ((*n)->exponent == 0 && (*n)->mantissa.length() < 6) {
      std::stringstream ss;
      ss << (*n)->mantissa;
      int m;
      ss >> m;
      s.insert(std::make_pair(p, m));
      return s;
    }
  }
  p.insert(std::make_pair(r, 1));
  s.insert(std::make_pair(p, 1));
  return s;
}

void test_ringularity(ast_real const *r1, ast_real const *r2) {
  sum diff = add(ringalize(r1), neg(ringalize(r2)));
  if (diff.empty()) return;
  std::cerr << "Warning: " << dump_real(r1) << " and " << dump_real(r2) << " are not trivially equal.\n";
  std::cerr << "         Difference: ";
  for(sum::const_iterator i = diff.begin(), i_end = diff.end(); i != i_end; ++i) {
    std::cerr << (i->second > 0 ? " +" : " ") << i->second;
    for(product::const_iterator j = i->first.begin(), j_end = i->first.end(); j != j_end; ++j) {
      std::cerr << " * (" << dump_real(j->first) << ')';
      if (j->second != 1) std::cerr << '^' << j->second;
    }
  }
  std::cerr << '\n';
}
