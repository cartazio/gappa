#include <set>
#include "ast.hpp"
#include "numbers/interval_ext.hpp"

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

void make_variables_real() {
  for(store_t::const_iterator i = store.begin(), end = store.end(); i != end; ++i) {
    variable *v = (*i)->var;
    if (v && !v->type) v->type = interval_real;
  }
}

template< class T >
struct cache {
  T *find(T const &);
 private:
  struct less_t {
    bool operator()(T const *v1, T const *v2) { return *v1 < *v2; }
  };
  typedef std::set< T *, less_t > store_t;
  store_t store;
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

static cache< ast_real > ast_real_cache;
ast_real *normalize(ast_real const &v) { return ast_real_cache.find(v); }
static cache< ast_number > ast_number_cache;
ast_number *normalize(ast_number const &v) { return ast_number_cache.find(v); }
