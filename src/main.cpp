#include <iostream>
#include "ast.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "basic_proof.hpp"
#include "interval.hpp"

program_t program;
graph_t graph;

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
  node_set const &c = graph.get_conclusions();
  std::cout << c.size() << " conclusions" << std::endl;
  for(node_set::const_iterator i = c.begin(); i != c.end(); ++i) {
    /*
    if (property_bound *r = boost::get< property_bound >(&(*i)->res))
      std::cout << "* " << r->var->name->name << " in " << r->bnd << std::endl;
    else if (property_error *r = boost::get< property_error >(&(*i)->res)) {
      static char const *type[] = { "ABS", "REL" };
      std::cout << "* " << type[r->error] << '(' << r->var->name->name << ", " << *r->real << ") in " << r->err << std::endl;
    } else assert(false);
    */
    generator *g = generate_basic_proof((*i)->hyp, (*i)->res);
    if (!g) continue;
    if (property_bound *r = boost::get< property_bound >(&g->res))
      std::cout << r->var->name->name << " in " << r->bnd << std::endl;
    else if (property_error *r = boost::get< property_error >(&g->res)) {
      static char const *type[] = { "ABS", "REL" };
      std::cout << type[r->error] << '(' << r->var->name->name << ", ...) in " << r->err << std::endl;
    } else assert(false);
  }
}
