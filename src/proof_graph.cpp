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

void node::insert_pred(node *n) {
  pred.push_back(n);
  n->insert_succ(this);
}

void node::insert_succ(node *n) {
  succ.insert(n);
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
  nodes.insert(n);
}

void graph_t::erase(node *n) {
  if (n->type == CONCLUSION) conclusions.erase(n);
  nodes.erase(n);
}

node *graph_t::find_compatible_node(property_vect const &hyp, property const &res) const {
  for(node_set::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i)
    if (hyp > (*i)->hyp && (*i)->res > res) return *i;
  if (father != NULL) return father->find_compatible_node(hyp, res);
  return NULL;
}

graph_layer::graph_layer() {
  graph_t *old_graph = graph;
  graph = new graph_t;
  graph->father = old_graph;
}

graph_layer::~graph_layer() {
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

void graph_layer::flatten() const {
  graph_t *old_graph = graph->father;
  assert(graph != NULL);
  for(node_set::const_iterator i = graph->nodes.begin(), end = graph->nodes.end(); i != end; ++i)
    old_graph->nodes.insert(*i);
  graph->nodes.clear();
}
