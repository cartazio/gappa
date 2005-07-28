#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/schemes.hpp"

#include <algorithm>
#include <cassert>
#include <set>
#include <sstream>

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

std::string dump_real(ast_real const *r, int prio) {
  if (r->name)
    return r->name->name;
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r)) {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0) return "0";
    if (n.exponent == 0) return m;
    std::stringstream s;
    s << m << (n.base == 2 ? 'b' : 'e') << n.exponent;
    return s.str();
  }
  if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "-+-*/";
    static bool const pr[] = { 2, 0, 0, 1, 1 };
    std::string s;
    if (o->ops.size() == 1)
      s = op[o->type] + dump_real(o->ops[0], pr[o->type]);
    else
      s = dump_real(o->ops[0], pr[o->type]) + ' ' + op[o->type] + ' ' + dump_real(o->ops[1], pr[o->type] + 1);
    if (prio <= pr[o->type]) return s;
    return '(' + s + ')';
  }
  if (rounded_real const *rr = boost::get< rounded_real const >(r))
    return '<' + rr->rounding->name() + ">(" + dump_real(rr->rounded, 0) + ')';
  assert(false);
  return "...";
}

default_rounding_generator::default_rounding_generator(std::string const &name, rounding_class const *r)
  : rnd(r)
{
  ast_ident *id = ast_ident::find(name);
  id->id_type = REAL_RND;
  id->rnd = this;
}
