#include <algorithm>
#include <set>
#include "ast.hpp"
#include "basic_proof.hpp"
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
    if ((*i)->id_type != PROG_VAR) continue;
    variable *v = (*i)->var;
    if (v && !v->type) v->type = interval_real_desc;
  }
}

template< class T >
class cache {
  struct less_t {
    bool operator()(T const *v1, T const *v2) { return *v1 < *v2; }
  };
  typedef std::set< T *, less_t > store_t;
  store_t store;
 public:
  T *find(T const &, void (*)(T *) = NULL);
  typedef typename store_t::iterator iterator;
  iterator begin() const { return store.begin(); }
  iterator end  () const { return store.end  (); }
};

template< class T >
T *cache< T >::find(T const &v, void (*f)(T *)) {
  typename store_t::const_iterator i = store.find(const_cast< T * >(&v));
  T *ptr;
  if (i == store.end()) {
    ptr = new T(v);
    store.insert(ptr);
    if (f) (*f)(ptr);
  } else ptr = *i;
  return ptr;
}

static cache< ast_number > ast_number_cache;
ast_number *normalize(ast_number const &v) { return ast_number_cache.find(v); }
static cache< ast_real > ast_real_cache;
ast_real *normalize(ast_real const &v) { return ast_real_cache.find(v, &add_basic_scheme); }

void set_default_schemes() {
  std::for_each(ast_real_cache.begin(), ast_real_cache.end(), &add_basic_scheme);
}
