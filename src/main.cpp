#include <iostream>
#include "ast.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "basic_proof.hpp"
#include "interval_ext.hpp"
#include "functions/float.hpp"

static void initialize_functions() {
  initialize_add();
  initialize_sub();
  initialize_mul();
}

extern int yyparse(void);
extern node *generate_proof(property_vect const &hyp, property const &res);

int main() {
  initialize_functions();
  yyparse();
  std::cout << conclusions.size() << " conclusions" << std::endl;
  for(node_set::const_iterator i = conclusions.begin(), end = conclusions.end(); i != end; ++i) {
    graph_layer layer;
    node *n = generate_proof((*i)->hyp, (*i)->res);
    if (!n) continue;
    property &p = n->res;
    if (p.type == PROP_BND)
      std::cout << p.var->name->name << " in ";
    else if (p.type == PROP_ABS || p.type == PROP_REL) {
      std::cout << (p.type == PROP_ABS ? "ABS(" : "REL(") << p.var->name->name << ", ...) in ";
    } else assert(false);
    std::cout << p.bnd << std::endl;
    layer.flatten();
  }
}
