#include "parser/ast.hpp"
#include "proofs/schemes.hpp"

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
  iterator i = store.find(const_cast< T * >(&v));
  T *ptr;
  if (i == store.end()) {
    ptr = new T(v);
    store.insert(ptr);
  } else ptr = *i;
  return ptr;
}

bool ast_real::operator==(ast_real const &v) const {
  if (boost::get< undefined_real const >(this) && boost::get< undefined_real const >(&v))
    return name == v.name;
  return ast_real_aux::operator==(static_cast< ast_real_aux const & >(v));
}

bool ast_real::operator<(ast_real const &v) const {
  if (boost::get< undefined_real const >(this) && boost::get< undefined_real const >(&v))
    return name < v.name;
  return ast_real_aux::operator<(static_cast< ast_real_aux const & >(v));
}

static cache< ast_number > ast_number_cache;
ast_number *normalize(ast_number const &v) { return ast_number_cache.find(v); }
static cache< ast_real > ast_real_cache;
ast_real *normalize(ast_real const &v) { return ast_real_cache.find(v); }

void clear_schemes() {
  for(cache< ast_real >::iterator i = ast_real_cache.begin(), i_end = ast_real_cache.end(); i != i_end; ++i) {
    proof_scheme_list *&s = (*i)->schemes;
    if (s) {
      for(proof_scheme_list::const_iterator j = s->begin(), j_end = s->end(); j != j_end; ++j)
        delete *j;
      delete s;
      s = NULL;
    }
  }
}

std::string dump_real(ast_real const *r) {
  if (r->name)
    return r->name->name;
  else
    return "...";
}
