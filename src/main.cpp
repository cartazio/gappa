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

template< class T >
int map_finder(std::map< T, int > &m, T const &k) {
  typename std::map< T, int >::const_iterator it = m.find(k);
  if (it != m.end()) return -it->second;
  int id = m.size() + 1;
  m.insert(std::make_pair(k, id));
  return id;
}

typedef std::map< ast_real const *, int > real_map;
static real_map displayed_reals;

int display(ast_real const *r) {
  int r_id = map_finder(displayed_reals, r);
  if (r_id < 0) return -r_id;
  auto_flush plouf;
  plouf << "Definition r" << r_id << " := ";
  if (variable *const *v = boost::get< variable *const >(r))
    plouf << '_' << (*v)->name->name;
  else if (ast_number *const *n = boost::get< ast_number *const >(r))
    if ((*n)->base == 0) plouf << '0';
    else plouf << (*n)->mantissa << ((*n)->base == 2 ? 'b' : 'e') << (*n)->exponent;
  else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "-+-*/";
    if (o->ops.size() == 1)
      plouf << '(' << op[o->type] << " r" << display(o->ops[0]) << ")%R";
    else
      plouf << "(r" << display(o->ops[0]) << ' ' << op[o->type] << " r" << display(o->ops[1]) << ")%R";
  } else assert(false);
  plouf << ".\n";
  return r_id;
}

typedef std::map< std::string, int > property_map; // (not so) bastard way of doing it
static property_map displayed_properties;

int display(property const &p) {
  std::stringstream s;
  std::string const &name = p.var->name->name;
  if (p.type == PROP_BND)
    s << name;
  else if (p.type == PROP_ABS || p.type == PROP_REL)
    s << (p.type == PROP_ABS ? "ABS" : "REL") << "(_" << name << ", r" << display(p.real) << ')';
  else assert(false);
  s << " in " << p.bnd;
  std::string s_ = s.str();
  int p_id = map_finder(displayed_properties, s_);
  if (p_id < 0) return -p_id;
  std::cout << "Definition p" << p_id << " := " << s_ << '\n';
  return p_id;
}

typedef std::map< node *, int > node_map;
static node_map displayed_nodes;

int display(node *n) {
  int n_id = map_finder(displayed_nodes, n);
  if (n_id < 0) return -n_id;
  static char const *const node_ids[] = { "HYPOTHESIS", "CONCLUSION", "THEOREM", "MODUS", "UNION", "OTHER" };
  auto_flush plouf;
  plouf << "Lemma l" << n_id << ": ";
  for(property_vect::const_iterator i = n->hyp.begin(), end = n->hyp.end(); i != end; ++i)
    plouf << 'p' << display(*i) << " -> ";
  plouf << 'p' << display(n->res) << ".\n";
  plouf << " intros";
  for(int i = 0, l = n->hyp.size(); i < l; ++i) plouf << " h" << i;
  plouf << ".\n";
  if (n->type == THEOREM) {
    plouf << " apply " << static_cast< node_theorem * >(n)->name << '.';
    for(int i = 0, l = n->hyp.size(); i < l; ++i) plouf << " exact h" << i << '.';
    plouf << "\nQed.\n";
  } else {
    plouf << node_ids[n->type];
    if (n->type == OTHER)
      plouf << " (relabs)";
    for(node_vect::const_iterator i = n->pred.begin(), end = n->pred.end(); i != end; ++i)
      plouf << " l" << display(*i);
    plouf << '\n';
  }
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
