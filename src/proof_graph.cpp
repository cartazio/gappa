/*

The whole proof graph is in fact composed of graph layers. These layers
are in a list. Nodes are created in the current current layer (called
graph). Their predecessors are necessarily in the same layer or in
layers below. Nodes are deleted at the same time the layer is.

*/

#include "proof_graph.hpp"

node_set conclusions;
graph_t base_graph;
graph_t *graph = &base_graph;

node::node(node_id t): type(t) {
  graph->insert(this);
}

void node::insert_succ(node *n) {
  succ.insert(n);
}

void node::insert_pred(node *n) {
  pred.push_back(n);
  n->insert_succ(this);
}

void node::remove_succ(node *n) {
  succ.erase(n);
}

void node::replace_pred(node *o, node *n) {
  for(int i = pred.size() - 1; i >= 0; i--)
    if (pred[i] == o) {
      o->remove_succ(this);
      n->insert_succ(this);
      pred[i] = n;
    }
}

void graph_t::insert(node *n) {
  if (n->type == CONCLUSION) { assert(this == &base_graph); conclusions.insert(n); }
  else nodes.insert(n);
}

void graph_t::erase(node *n) {
  if (n->type == CONCLUSION) conclusions.erase(n);
  else nodes.erase(n);
}

node *graph_t::find_compatible_node(property_vect const &hyp, property const &res) const {
  for(node_set::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i)
    if (hyp.implies((*i)->hyp) && (*i)->res.implies(res)) return *i;
  if (father) return father->find_compatible_node(hyp, res);
  return NULL;
}

bool graph_t::has_compatible_hypothesis(ast_real const *r) const {
  for(node_set::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i)
    if ((*i)->type == HYPOTHESIS && (*i)->res.real == r) return true;
  if (father) return father->has_compatible_hypothesis(r);
  return false;
}

static void delete_top_graph() {
  // the two loops can't be merged since a successor could then be removed on an already deleted node
  for(node_set::const_iterator i = graph->nodes.begin(), end = graph->nodes.end(); i != end; ++i)
    for(node_vect::iterator j = (*i)->pred.begin(), end = (*i)->pred.end(); j != end; ++j)
      (*j)->remove_succ(*i);
  for(node_set::const_iterator i = graph->nodes.begin(), end = graph->nodes.end(); i != end; ++i)
    delete *i;
  graph_t *old_graph = graph->father;
  delete graph;
  graph = old_graph;
}

static void flatten_top_graph() {
  assert(graph);
  graph_t *old_graph = graph->father;
  assert(old_graph);
  for(node_set::const_iterator i = graph->nodes.begin(), end = graph->nodes.end(); i != end; ++i)
    old_graph->nodes.insert(*i);
  graph->nodes.clear();
}

graph_layer::graph_layer() {
  graph_t *old_graph = graph;
  graph = new graph_t;
  graph->father = old_graph;
}

graph_layer::~graph_layer() {
  delete_top_graph();
}

void graph_layer::flatten() const {
  flatten_top_graph();
}

void graph_layer::store(graph_storage &s) const {
  s.stored_graph = graph;
  graph_t *old_graph = graph->father;
  graph = new graph_t;
  graph->father = old_graph;
}

graph_storage::~graph_storage() {
  if (!stored_graph) return;
  graph = stored_graph;
  flatten_top_graph();
  delete_top_graph();
}
