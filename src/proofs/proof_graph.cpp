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
}

void graph_t::insert(node *n) {
  if (n->type == CONCLUSION) { assert(this == &base_graph); conclusions.insert(n); }
  else nodes.insert(n);
}

void graph_t::erase(node *n) {
  if (n->type == CONCLUSION) conclusions.erase(n);
  else nodes.erase(n);
}

struct compatible_node_finder {
  property_vect const &hyp;
  ast_real const *real;
  interval const *bnd;
  node *best;
  compatible_node_finder(property_vect const &h, property const &r): hyp(h), real(r.real), bnd(&r.bnd), best(NULL) {}
  node *find(graph_t const *);
};

node *compatible_node_finder::find(graph_t const *g) {
  do {
    for(node_set::const_iterator i = g->nodes.begin(), end = g->nodes.end(); i != end; ++i) {
      node *n = *i;
      interval const *b = &n->res.bnd;
      if (n->res.real == real && (*b <= *bnd || (best && *b < *bnd)) && hyp.implies(n->hyp)) {
        bnd = b;
        best = n;
      }
    }
    g = g->father;
  } while (g);
  return best;
}

node *graph_t::find_compatible_node(property_vect const &hyp, property const &res) const {
  return compatible_node_finder(hyp, res).find(this);
}

bool graph_t::has_compatible_hypothesis(ast_real const *r) const {
  for(node_set::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i)
    if ((*i)->type == HYPOTHESIS && (*i)->res.real == r) return true;
  if (father) return father->has_compatible_hypothesis(r);
  return false;
}

node *graph_t::find_in_cache(property_vect const &hyp, property const &res) const {
  if (hyp == cache_dom) {
    node_map::const_iterator i = cache.find(res.real);
    if (i != cache.end() && i->second->res.bnd <= res.bnd) {
      node *n = i->second;
      assert(hyp.implies(n->hyp) && n->res.implies(res));
      return n;
    }
  }
  if (father) return father->find_in_cache(hyp, res);
  return NULL;
}

static void delete_top_graph() {
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
  if (graph->cache_dom == old_graph->cache_dom)
    old_graph->cache.insert(graph->cache.begin(), graph->cache.end());
  graph->cache.clear();
}

graph_layer::graph_layer(property_vect const &hyp) {
  graph_t *old_graph = graph;
  graph = new graph_t;
  graph->father = old_graph;
  graph->cache_dom = hyp;
}

graph_layer::~graph_layer() {
  delete_top_graph();
}

void graph_layer::flatten() const {
  flatten_top_graph();
}

void graph_layer::store(graph_storage &s) const {
  if (s.stored_graph) {
    s.stored_graph->father = graph;
    graph = s.stored_graph;
    delete_top_graph();
  }
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
