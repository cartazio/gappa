#include "parser/ast.hpp"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <map>
#include <sstream>

typedef std::map< ast_real const *, int > product;
typedef std::map< product, int > sum;
typedef std::pair< sum, sum > quotient;

static std::string dump_sum(sum const &s) {
  std::stringstream res;
  bool first_term = true;
  for(sum::const_iterator i = s.begin(), i_end = s.end(); i != i_end; ++i) {
    int coef = i->second;
    if (coef < 0) {
      coef = -coef;
      if (first_term) { res << '-'; first_term = false; }
      else res << " - ";
    } else {
      if (first_term) first_term = false;
      else res << " + ";
    }
    if (i->first.empty()) res << coef;
    else if (coef != 1) res << coef << " * ";
    bool first_factor = true;
    for(product::const_iterator j = i->first.begin(), j_end = i->first.end(); j != j_end; ++j) {
      if (first_factor) first_factor = false;
      else res << " * ";
      res << '(' << dump_real(j->first) << ')';
      if (j->second != 1) res << '^' << j->second;
    }
  }
  return res.str();
}

static product mul(product const &p1, product const &p2) {
  product res;
  product::const_iterator i1 = p1.begin(), e1 = p1.end(), i2 = p2.begin(), e2 = p2.end();
  while (i1 != e1 && i2 != e2) {
    ast_real const *r1 = i1->first, *r2 = i2->first;
    if (r1 < r2) res.insert(*i1++); else
    if (r2 < r1) res.insert(*i2++); else
    {
      int k = i1->second + i2->second;
      assert(r1 == r2 && k != 0);
      res.insert(std::make_pair(r1, k));
      ++i1;
      ++i2;
    }
  }
  res.insert(i1, e1);
  res.insert(i2, e2);
  return res;
}

static void add_factor(sum &res, product const &factor, int coef) {
  sum::iterator i = res.find(factor);
  if (i == res.end())
    res.insert(std::make_pair(factor, coef));
  else if ((i->second += coef) == 0)
    res.erase(i);
}

static sum neg(sum const &s) {
  sum res;
  for(sum::const_iterator i = s.begin(), end = s.end(); i != end; ++i)
    res.insert(std::make_pair(i->first, -i->second));
  return res;
}

static void fma(sum &res, sum const &s1, sum const &s2) {
  for(sum::const_iterator i = s1.begin(), i_end = s1.end(); i != i_end; ++i)
    for(sum::const_iterator j = s2.begin(), j_end = s2.end(); j != j_end; ++j)
      add_factor(res, mul(i->first, j->first), i->second * j->second);
}

static void fnma(sum &res, sum const &s1, sum const &s2) {
  for(sum::const_iterator i = s1.begin(), i_end = s1.end(); i != i_end; ++i)
    for(sum::const_iterator j = s2.begin(), j_end = s2.end(); j != j_end; ++j)
      add_factor(res, mul(i->first, j->first), - i->second * j->second);
}

static quotient neg(quotient const &q) {
  return quotient(neg(q.first), q.second);
}

static quotient add(quotient const &q1, quotient const &q2) {
  quotient res;
  fma(res.first, q1.first, q2.second);
  fma(res.first, q1.second, q2.first);
  fma(res.second, q1.second, q2.second);
  return res;
}

static sum sub_num(quotient const &q1, quotient const &q2) {
  sum res;
  fma(res, q1.first, q2.second);
  fnma(res, q1.second, q2.first);
  return res;
}

static quotient sub(quotient const &q1, quotient const &q2) {
  quotient res;
  fma(res.first, q1.first, q2.second);
  fnma(res.first, q1.second, q2.first);
  fma(res.second, q1.second, q2.second);
  return res;
}

static quotient mul(quotient const &q1, quotient const &q2) {
  quotient res;
  fma(res.first, q1.first, q2.first);
  fma(res.second, q1.second, q2.second);
  return res;
}

static quotient div(quotient const &q1, quotient const &q2) {
  std::cerr << "Warning: although present in a quotient, the expression "
            << dump_sum(q2.first) << " may have not been tested for non-zeroness.\n";
  quotient res;
  fma(res.first, q1.first, q2.second);
  fma(res.second, q1.second, q2.first);
  return res;
}

typedef std::map< ast_real const *, quotient > quotient_cache;
static quotient_cache cache;

static quotient const &ringalize(ast_real const *r);

static quotient fieldalize_aux(ast_real const *r) {
  if (real_op const *o = boost::get< real_op const >(r))
    switch (o->type) {
    case UOP_MINUS:	return neg(ringalize(o->ops[0]));
    case BOP_ADD:	return add(ringalize(o->ops[0]), ringalize(o->ops[1]));
    case BOP_SUB:	return sub(ringalize(o->ops[0]), ringalize(o->ops[1]));
    case BOP_MUL:	return mul(ringalize(o->ops[0]), ringalize(o->ops[1]));
    case BOP_DIV:    	return div(ringalize(o->ops[0]), ringalize(o->ops[1]));
    default: ;
    }
  sum s1, s2;
  product p;
  s2.insert(std::make_pair(p, 1));
  if (ast_number const *const *n = boost::get< ast_number const *const >(r)) {
    if ((*n)->base == 0) return quotient(s1, s2);
    if ((*n)->exponent == 0 && (*n)->mantissa.length() < 6) {
      std::stringstream ss;
      ss << (*n)->mantissa;
      int m;
      ss >> m;
      s1.insert(std::make_pair(p, m));
      return quotient(s1, s2);
    }
  }
  p.insert(std::make_pair(r, 1));
  s1.insert(std::make_pair(p, 1));
  return quotient(s1, s2);
}

static quotient const &ringalize(ast_real const *r) {
  quotient_cache::const_iterator i = cache.find(r);
  if (i != cache.end())
    return i->second;
  i = cache.insert(std::make_pair(r, fieldalize_aux(r))).first;
  return i->second;
}

void test_ringularity(ast_real const *r1, ast_real const *r2) {
  // std::cerr << "Testing " << dump_real(r1) << " -> " << dump_real(r2) << '\n';
  sum const &diff = sub_num(ringalize(r1), ringalize(r2));
  if (diff.empty()) return;
  std::cerr << "Warning: " << dump_real(r1) << " and " << dump_real(r2)
            << " are not trivially equal.\n";
  std::cerr << "         Difference: " << dump_sum(diff) << '\n';
}
