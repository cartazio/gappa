#include <iostream>
#include "ast.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "basic_proof.hpp"
#include "interval.hpp"

program_t program;

void initialize_functions() {
  ast_ident *id;
  type_id *args = new type_id[3];
  args[0] = FLOAT32;
  args[1] = FLOAT32;
  args[2] = UNDEFINED;
  type_id *ret = new type_id[2];
  ret[0] = FLOAT32;
  ret[1] = UNDEFINED;
  id = ast_ident::find("add32");
  id->fun = new function(id, BOP_ADD);
  id->fun->return_type = ret;
  id->fun->args_type = args;
  id = ast_ident::find("sub32");
  id->fun = new function(id, BOP_SUB);
  id->fun->return_type = ret;
  id->fun->args_type = args;
  id = ast_ident::find("mul32");
  id->fun = new function(id, BOP_MUL);
  id->fun->return_type = ret;
  id->fun->args_type = args;
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
