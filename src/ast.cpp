#include "ast.hpp"

#include <algorithm>
#include <cassert>
#include <set>

namespace {

struct ast_ident_lt {
  bool operator()(ast_ident const *i1, ast_ident const *i2) {
    return i1->name < i2->name;
  }
};

}

typedef std::set< ast_ident *, ast_ident_lt > store_t;
static store_t store;

ast_ident *ast_ident::find(std::string const &s) {
  ast_ident id(s);
  store_t::const_iterator i = store.find(&id);
  ast_ident *ptr;
  if (i == store.end()) {
    ptr = new ast_ident(id);
    store.insert(ptr);
  } else ptr = *i;
  return ptr;
}

template< class T >
class cache {
  struct less_t {
    bool operator()(T const *v1, T const *v2) { return *v1 < *v2; }
  };
  typedef std::set< T *, less_t > store_t;
  store_t store;
 public:
  T *find(T const &);
  typedef typename store_t::iterator iterator;
  iterator begin() const { return store.begin(); }
  iterator end  () const { return store.end  (); }
};

template< class T >
T *cache< T >::find(T const &v) {
  typename store_t::const_iterator i = store.find(const_cast< T * >(&v));
  T *ptr;
  if (i == store.end()) {
    ptr = new T(v);
    store.insert(ptr);
  } else ptr = *i;
  return ptr;
}

static cache< ast_number > ast_number_cache;
ast_number *normalize(ast_number const &v) { return ast_number_cache.find(v); }
static cache< ast_real > ast_real_cache;
ast_real *normalize(ast_real const &v) { return ast_real_cache.find(v); }

struct match_visitor: boost::static_visitor< bool > {
  bool visit(ast_real const *src, ast_real const *dst) const;
  template< typename T, typename U > bool operator()(T const &, U const &) const { return false; }
  template< typename T > bool operator()(T const &r1, T const &r2) const { return r1 == r2; }
  bool operator()(real_op const &r1, real_op const &r2) const;
  bool operator()(rounded_real const &r1, rounded_real const &r2) const;
  ast_real_vect &holders;
  match_visitor(ast_real_vect &h): holders(h) {}
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
  return r1.rounding == r2.rounding && visit(r1.rounded, r2.rounded);
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

bool match(ast_real const *src, ast_real const *dst, ast_real_vect &holders) {
  return match_visitor(holders).visit(src, dst);
}

struct rewrite_visitor: boost::static_visitor< ast_real const * > {
  ast_real const *visit(ast_real const *dst) const { return boost::apply_visitor(*this, *dst); }
  template< typename T > ast_real const *operator()(T const &r) const { return normalize(ast_real(r)); }
  ast_real const *operator()(real_op const &r) const;
  ast_real const *operator()(rounded_real const &r) const;
  ast_real const *operator()(placeholder i) const;
  ast_real_vect const &holders;
  rewrite_visitor(ast_real_vect const &h): holders(h) {}
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

ast_real const *rewrite(ast_real const *dst, ast_real_vect const &holders) {
  return rewrite_visitor(holders).visit(dst);
}
