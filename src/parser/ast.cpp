#include <algorithm>
#include <cassert>
#include <set>
#include <sstream>
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/schemes.hpp"

template< class T >
class cache {
  struct less_t {
    bool operator()(T const *v1, T const *v2) { return *v1 < *v2; }
  };
  typedef std::set< T *, less_t > store_t;
  store_t store;
 public:
  T *find(T const &);
  ~cache();
};

template< class T >
T *cache< T >::find(T const &v) {
  typename store_t::iterator i = store.find(const_cast< T * >(&v));
  T *ptr;
  if (i == store.end()) {
    ptr = new T(v);
    store.insert(ptr);
  } else ptr = *i;
  return ptr;
}

template< class T >
cache< T >::~cache() {
  for(typename store_t::iterator i = store.begin(), end = store.end(); i != end; ++i)
    delete *i;
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

static cache< ast_ident > ast_ident_cache;
ast_ident *ast_ident::find(std::string const &s) { return ast_ident_cache.find(ast_ident(s)); }
static cache< ast_number > ast_number_cache;
ast_number *normalize(ast_number const &v) { return ast_number_cache.find(v); }
static cache< ast_real > ast_real_cache;
ast_real *normalize(ast_real const &v) { return ast_real_cache.find(v); }

std::string dump_real(ast_real const *r, unsigned prio) {
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
    if (o->type == ROP_FUN) {
      std::string s = '[' + o->fun->name() + "](" + dump_real(o->ops[0], 0);
      for(ast_real_vect::const_iterator i = ++(o->ops.begin()), end = o->ops.end(); i != end; ++i)
        s += ", " + dump_real(*i, 0);
      return s + ')';
    }
    static char const op[] = "X-X+-*/XX";
    static unsigned const pr[] = { 0, 2, 0, 0, 0, 1, 1, 0, 0 };
    std::string s = dump_real(o->ops[0], pr[o->type]);
    if (o->ops.size() == 1)
      if (o->type == UOP_ABS) {
        s = '|' + s + '|';
        prio = 0;
      } else
        s = op[o->type] + s;
    else
      s = s + ' ' + op[o->type] + ' ' + dump_real(o->ops[1], pr[o->type] + 1);
    if (prio <= pr[o->type]) return s;
    return '(' + s + ')';
  }
  assert(false);
  return "...";
}

function_generator::function_generator(char const *name) {
  ast_ident::find(name)->fun = this;
}

function_class const *default_function_generator::operator()(function_params const &p) const {
  return p.empty() ? fun : NULL;
}

interval function_class::round                      (interval const &, std::string &) const { return interval(); }
interval function_class::enforce                    (interval const &, std::string &) const { return interval(); }
interval function_class::absolute_error_from_real   (interval const &, std::string &) const { return interval(); }
interval function_class::relative_error_from_real   (interval const &, std::string &) const { return interval(); }
interval function_class::absolute_error_from_rounded(interval const &, std::string &) const { return interval(); }
interval function_class::relative_error_from_rounded(interval const &, std::string &) const { return interval(); }
