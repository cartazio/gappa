#include <iostream>
#include "ast.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "basic_proof.hpp"
#include "interval.hpp"
#include "function.hpp"
#include "functions/float.hpp"

static void initialize_functions() {
  initialize_add();
  initialize_sub();
  initialize_mul();
}

extern int yyparse(void);

int main() {
  initialize_functions();
  yyparse();
  std::cout << conclusions.size() << " conclusions" << std::endl;
  for(node_set::const_iterator i = conclusions.begin(), end = conclusions.end(); i != end; ++i) {
    graph_layer layer;
    node *n = generate_basic_proof((*i)->hyp, (*i)->res);
    if (!n) continue;
    if (property_bound *r = boost::get< property_bound >(&n->res))
      std::cout << r->var->name->name << " in " << r->bnd << std::endl;
    else if (property_error *r = boost::get< property_error >(&n->res)) {
      static char const *type[] = { "ABS", "REL" };
      std::cout << type[r->error] << '(' << r->var->name->name << ", ...) in " << r->err << std::endl;
    } else assert(false);
    layer.flatten();
  }
}
