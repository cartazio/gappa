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
    if (!v) continue;
    if (v->type == UNDEFINED) v->type = &interval_real_desc;
  }
}
