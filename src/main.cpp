#include <iostream>
#include <map>
#include <sstream>
#include "ast.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "basic_proof.hpp"
#include "numbers/interval_ext.hpp"

extern int yyparse(void);
extern node *generate_proof(property_vect const &hyp, property const &res);
extern node *triviality;

struct node_theorem: node {
  char const *name;
  node_theorem(int nb, property const *h, property const &p, char const *n);
};

struct auto_flush: std::stringstream {
  ~auto_flush() { std::cout << this->str(); }
};

typedef std::map< ast_real const *, int > real_map;
static real_map displayed_reals;

int display(ast_real const *r) {
  real_map::const_iterator it = displayed_reals.find(r);
  if (it != displayed_reals.end()) return it->second;
  int r_id = displayed_reals.size();
  displayed_reals.insert(std::make_pair(r, r_id));
  auto_flush plouf;
  plouf << "Definition r" << r_id << " := ";
  if (variable *const *v = boost::get< variable *const >(r))
    plouf << (*v)->name->name;
  else if (ast_number *const *n = boost::get< ast_number *const >(r))
    if ((*n)->base == 0) plouf << '0';
    else plouf << (*n)->mantissa << ((*n)->base == 2 ? 'b' : 'e') << (*n)->exponent;
  else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "-+-*/";
    plouf << op[o->type];
    for(ast_real_vect::const_iterator i = o->ops.begin(), end = o->ops.end(); i != end; ++i)
      plouf << " r" << display(*i);
  } else assert(false);
  plouf << '\n';
  return r_id;
}

static int property_nb = 0;

int display(property const &p) {
  auto_flush plouf;
  int p_id = property_nb++;
  plouf << "Definition p" << p_id << " := ";
  std::string const &name = p.var->name->name;
  if (p.type == PROP_BND)
    plouf << name;
  else if (p.type == PROP_ABS || p.type == PROP_REL)
    plouf << (p.type == PROP_ABS ? "ABS(" : "REL(") << name << ", r" << display(p.real) << ')';
  else assert(false);
  plouf << " in " << p.bnd << '\n';
  return p_id;
}

typedef std::map< node *, int > node_map;
static node_map displayed_nodes;

int display(node *n) {
  node_map::const_iterator it = displayed_nodes.find(n);
  if (it != displayed_nodes.end()) return it->second;
  int n_id = displayed_nodes.size();
  displayed_nodes.insert(std::make_pair(n, n_id));
  static char const *const node_ids[] = { "HYPOTHESIS", "CONCLUSION", "THEOREM", "MODUS", "UNION", "OTHER" };
  auto_flush plouf;
  plouf << "Lemma l" << n_id << ": ";
  for(property_vect::const_iterator i = n->hyp.begin(), end = n->hyp.end(); i != end; ++i)
    plouf << 'p' << display(*i) << " -> ";
  plouf << 'p' << display(n->res) << "\n " << node_ids[n->type];
  if (n->type == THEOREM)
    plouf << " (" << static_cast< node_theorem * >(n)->name << ')';
  else if (n->type == OTHER)
    plouf << " (relabs)";
  for(node_vect::const_iterator i = n->pred.begin(), end = n->pred.end(); i != end; ++i)
    plouf << " l" << display(*i);
  plouf << '\n';
  return n_id;
}

int main() {
  yyparse();
  for(node_set::const_iterator i = conclusions.begin(), end = conclusions.end(); i != end; ++i) {
    graph_layer layer;
    node *n = generate_proof((*i)->hyp, (*i)->res);
    if (!n) continue;
    property const &p = n->res;
    std::string const &name = p.var->name->name;
    if (p.type == PROP_BND)
      std::cout << name;
    else if (p.type == PROP_ABS || p.type == PROP_REL)
      std::cout << (p.type == PROP_ABS ? "ABS(" : "REL(") << name << ", ...)";
    else assert(false);
    std::cout << " in " << p.bnd << std::endl;
    layer.flatten();
    (*i)->insert_pred(n);
  }
  std::cout << "\n\n";
  for(node_set::const_iterator i = conclusions.begin(), end = conclusions.end(); i != end; ++i) {
    node_vect const &v = (*i)->pred;
    if (v.empty()) continue;
    display(v[0]);
  }
}
