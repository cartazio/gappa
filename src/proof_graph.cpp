#include "proof_graph.hpp"

node::node(node_id t): type(t) {
  graph.insert(this);
}

node::~node() {
  assert(succ.size() == 0);
  for(int i = pred.size() - 1; i >= 0; i--) pred[i]->remove_succ(this);
  graph.erase(this);
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
  if (n->type == CONCLUSION) conclusions.insert(n);
  nodes.insert(n);
}

void graph_t::erase(node *n) {
  if (n->type == CONCLUSION) conclusions.erase(n);
  nodes.erase(n);
}

node *graph_t::find_compatible_node(property_vect const &hyp, property const &res) const {
  for(node_set::const_iterator i = nodes.begin(); i != nodes.end(); ++i)
    if (hyp > (*i)->hyp && (*i)->res > res) return *i;
  return false;
}
