#include <algorithm>
#include <cassert>
#include <set>
#include <sstream>
#include "utils.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/schemes.hpp"

extern bool parameter_rfma;
link_map accurates, approximates;

template< class T >
class cache {
  struct less_t {
    bool operator()(T const *v1, T const *v2) { return *v1 < *v2; }
  };
  typedef std::set< T *, less_t > store_t;
  store_t store;
 public:
  T *find(T const &, bool * = NULL);
  ~cache();
};

template< class T >
T *cache< T >::find(T const &v, bool *b) {
  typename store_t::iterator i = store.find(const_cast< T * >(&v));
  T *ptr;
  bool c = i == store.end();
  if (b) *b = c;
  if (c) {
    ptr = new T(v);
    store.insert(ptr);
  } else ptr = *i;
  return ptr;
}

template< class T >
cache< T >::~cache() {
  #ifdef LEAK_CHECKER
  for(typename store_t::iterator i = store.begin(), end = store.end(); i != end; ++i)
    delete *i;
  #endif
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

static bool set_flags_constant(real_op const *p)
{
  if ((p->type == BOP_SUB || p->type == BOP_DIV) && p->ops[0] == p->ops[1]) return true;
  for (ast_real_vect::const_iterator i = p->ops.begin(), end = p->ops.end(); i != end; ++i)
    if (!(*i)->is_constant) return false;
  return true;
}

static bool set_flags_placeholder(real_op const *p)
{
  for (ast_real_vect::const_iterator i = p->ops.begin(), end = p->ops.end(); i != end; ++i)
    if ((*i)->has_placeholder) return true;
  return false;
}

void set_flags(ast_real *r, real_op const *p)
{
  r->is_constant = set_flags_constant(p);
  r->has_placeholder = set_flags_placeholder(p);
}

ast_real const *unround(real_op_type type, ast_real_vect const &v) {
  switch (type) {
  case UOP_ID: return v[0];
  case COP_FMA:
    if (!parameter_rfma)
      return normalize(ast_real(real_op(normalize(ast_real(real_op(v[0], BOP_MUL, v[1]))), BOP_ADD, v[2])));
    else
      return normalize(ast_real(real_op(v[2], BOP_ADD, normalize(ast_real(real_op(v[0], BOP_MUL, v[1]))))));
  default: return normalize(ast_real(real_op(type, v)));
  }  
}

static cache< ast_ident > ast_ident_cache;
ast_ident *ast_ident::find(std::string const &s) { return ast_ident_cache.find(ast_ident(s)); }
static cache< ast_number > ast_number_cache;
ast_number *normalize(ast_number const &v) { return ast_number_cache.find(v); }
static cache< ast_real > ast_real_cache;
ast_real *normalize(ast_real const &v) {
  bool b;
  ast_real *p = ast_real_cache.find(v, &b);
  if (!b) return p;
  real_op *o = boost::get< real_op >(p);
  if (!o || !o->fun || o->fun->type == ROP_UNK) return p;
  ast_real const *a = unround(o->fun->type, o->ops);
  accurates[p].insert(a);
  approximates[a].insert(p);
  return p;
}

ast_number const *token_zero, *token_one;

RUN_ONCE(load_numbers) {
  ast_number num;
  num.base = 0;
  num.exponent = 0;
  token_zero = normalize(num);
  num.base = 10;
  num.exponent = 0;
  num.mantissa = "+1";
  token_one = normalize(num);
}

std::string dump_real(ast_real const *r, unsigned prio)
{
  if (hidden_real const *h = boost::get< hidden_real const >(r))
    r = h->real;
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
  if (placeholder const *i = boost::get< placeholder const >(r)) {
    return std::string(1, '?') + (char)(i->num + '1');
  }
  if (real_op const *o = boost::get< real_op const >(r)) {
    if (o->type == ROP_FUN) {
      std::string s = '[' + o->fun->name() + "](" + dump_real(o->ops[0], 0);
      for(ast_real_vect::const_iterator i = ++(o->ops.begin()), end = o->ops.end(); i != end; ++i)
        s += ", " + dump_real(*i, 0);
      return s + ')';
    }
    static char const op[] = "X-XX+-*/XX";
    static unsigned const pr[] = { 0, 3, 0, 0, 0, 0, 1, 2, 0, 0 };
    std::string s = dump_real(o->ops[0], pr[o->type]);
    if (o->ops.size() == 1)
      switch (o->type) {
      case UOP_ABS: {
        s = '|' + s + '|';
        prio = 0;
        break; }
      case UOP_SQRT: {
        s = "sqrt(" + s + ')';
        prio = 0;
        break; }
      default:
        s = op[o->type] + s;
      }
    else
      s = s + ' ' + op[o->type] + ' ' + dump_real(o->ops[1], pr[o->type] + 1);
    if (prio <= pr[o->type]) return s;
    return '(' + s + ')';
  }
  assert(false);
  return "...";
}

std::string dump_real(predicated_real const &r) {
  std::stringstream s;
  std::string v = dump_real(r.real());
  switch (r.pred()) {
  case PRED_BND: s << "BND(" << v << ')'; break;
  case PRED_ABS: s << "ABS(" << v << ')'; break;
  case PRED_REL: s << "REL(" << v << ", " << dump_real(r.real2()) << ')'; break;
  case PRED_FIX: s << "FIX(" << v << ')'; break;
  case PRED_FLT: s << "FLT(" << v << ')'; break;
  case PRED_NZR: s << "NZR(" << v << ')'; break;
  default: assert(false);
  }
  return s.str();
}

std::string dump_property(property const &p) {
  std::stringstream s;
  std::string r = dump_real(p.real.real());
  switch (p.real.pred()) {
  case PRED_BND: s << "BND(" << r << ", " << p.bnd() << ')'; break;
  case PRED_ABS: s << "ABS(" << r << ", " << p.bnd() << ')'; break;
  case PRED_REL: s << "REL(" << r << ", " << dump_real(p.real.real2()) << ", " << p.bnd() << ')'; break;
  case PRED_FIX: s << "FIX(" << r << ", " << p.cst() << ')'; break;
  case PRED_FLT: s << "FLT(" << r << ", " << p.cst() << ')'; break;
  case PRED_NZR: s << "NZR(" << r << ')'; break;
  default: assert(false);
  }
  return s.str();
}

function_generator::function_generator(char const *name) {
  ast_ident * i = ast_ident::find(name);
  assert(i->type == ID_NONE);
  i->type = ID_FUN;
  i->fun = this;
}

function_class const *default_function_generator::operator()(function_params const &p) const {
  return p.empty() ? fun : NULL;
}

interval function_class::round                         (interval const &, std::string &) const { assert(false); }
interval function_class::enforce                       (interval const &, std::string &) const { assert(false); }
interval function_class::absolute_error                                  (std::string &) const { assert(false); }
interval function_class::absolute_error_from_exact_bnd (interval const &, std::string &) const { assert(false); }
interval function_class::absolute_error_from_exact_abs (interval const &, std::string &) const { assert(false); }
interval function_class::absolute_error_from_approx_bnd(interval const &, std::string &) const { assert(false); }
interval function_class::absolute_error_from_approx_abs(interval const &, std::string &) const { assert(false); }
interval function_class::relative_error_from_exact_bnd (interval const &, std::string &) const { assert(false); }
interval function_class::relative_error_from_exact_abs (interval const &, std::string &) const { assert(false); }
interval function_class::relative_error_from_approx_bnd(interval const &, std::string &) const { assert(false); }
interval function_class::relative_error_from_approx_abs(interval const &, std::string &) const { assert(false); }
