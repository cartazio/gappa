#include <iostream>
#include "ast.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "basic_proof.hpp"
#include "numbers/interval_ext.hpp"

extern int yyparse(void);
extern node *generate_proof(property_vect const &hyp, property const &res);

int main() {
  yyparse();
  for(node_set::const_iterator i = conclusions.begin(), end = conclusions.end(); i != end; ++i) {
    graph_layer layer;
    node *n = generate_proof((*i)->hyp, (*i)->res);
    if (!n) continue;
    property &p = n->res;
    std::string const &name = p.var->name->name;
    if (p.type == PROP_BND)
      std::cout << name;
    else if (p.type == PROP_ABS || p.type == PROP_REL)
      std::cout << (p.type == PROP_ABS ? "ABS(" : "REL(") << name << ", ...)";
    else assert(false);
    std::cout << " in " << p.bnd << std::endl;
    layer.flatten();
  }
}
