#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/proof_graph.hpp"

graph_t *top_graph = NULL;
node_vect *top_layer = NULL;

property_vect const &node::get_hypotheses() const {
  static property_vect dummy;
  return dummy;
}

node_vect const &node::get_subproofs() const {
  static node_vect dummy;
  return dummy;
}

result_node::result_node(node_id t, property const &p, bool b): node(t), res(p) {
  if (!b) return;
  assert(top_graph);
  top_graph->insert(this);
  if (top_layer)
    top_layer->push_back(this);
}

theorem_node::theorem_node(int nb, property const h[], property const &p, std::string const &n)
    : result_node(THEOREM, p), name(n) {
  for(int i = 0; i < nb; ++i) hyp.push_back(h[i]);
}

typedef std::map< ast_real const *, interval > property_map;

// intersecting shouldn't create a wrong proof: by design
// (for an hypothesis map) - the hypotheses are all satisfiable, hence their intersection too
// (for a result map) - the results have been generated at the same time, they are identical
static void fill_property_map(property_map &m, property const &p) {
  property_map::iterator pki = m.find(p.real);
  if (pki != m.end())
    pki->second = intersect(pki->second, p.bnd);
  else
    m.insert(std::make_pair(p.real, p.bnd));
}

static void fill_property_map(property_map &m, property_vect const &v) {
  for(property_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i)
    fill_property_map(m, *i);
}

static void fill_property_map(property_map &m, node *n) {
  if (n->type == HYPOTHESIS)
    fill_property_map(m, n->get_result());
  else
    fill_property_map(m, n->get_hypotheses());
}

static void fill_property_vect(property_vect &v, property_map const &m) {
  for(property_map::const_iterator i = m.begin(), end = m.end(); i != end; ++i)
    v.push_back(property(i->first, i->second));
}

modus_node::modus_node(int nb, node *nodes[], node *n)
    : dependent_node(MODUS, n->get_result()) {
  assert(n->type != INTERSECTION);
  insert_pred(n);
  property_map pmap, rmap;
  for(int i = 0; i < nb; ++i) {
    node *m = nodes[i];
    fill_property_map(rmap, m->get_result());
    fill_property_map(pmap, m);
    if (m->type == HYPOTHESIS) continue;
    insert_pred(m);
  }
  property_vect const &n_hyp = n->get_hypotheses();
  for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end(); j != j_end; ++j) {
    property const &p = *j;
    property_map::iterator pki = rmap.find(p.real); // is the hypothesis a result?
    if (pki != rmap.end() && pki->second <= p.bnd) continue;
    fill_property_map(pmap, p);
  }
  fill_property_vect(hyp, pmap);
}

class intersection_node: public dependent_node {
  static property helper(node *n1, node *n2);
 public:
  intersection_node(node *n1, node *n2);
};

property intersection_node::helper(node *n1, node *n2) {
  property const &res1 = n1->get_result(), &res2 = n2->get_result();
  assert(res1.real == res2.real);
  return property(res1.real, intersect(res1.bnd, res2.bnd));
}

intersection_node::intersection_node(node *n1, node *n2)
    : dependent_node(INTERSECTION, helper(n1, n2)) {
  interval const &i1 = n1->get_result().bnd, &i2 = n2->get_result().bnd;
  if (lower(i1) > lower(i2)) std::swap(n1, n2);
  // to simplify the graph, no intersection should be nested
  if (n1->type == INTERSECTION) n1 = n1->get_subproofs()[0];
  if (n2->type == INTERSECTION) n2 = n2->get_subproofs()[1];
  // by disallowing both nodes to be hypotheses, we are sure that even if the
  // output real is also an input, it is a meaningful input; enforced by the parser
  assert(n1->type != HYPOTHESIS || n2->type != HYPOTHESIS);
  insert_pred(n1);
  insert_pred(n2);
  property_map pmap;
  fill_property_map(pmap, n1);
  fill_property_map(pmap, n2);
  fill_property_vect(hyp, pmap);
}

graph_t::graph_t(graph_t *f, property_vect const &h): hyp(h) {
  if (f) {
    assert(hyp.implies(f->hyp));
    known_reals = f->known_reals;
    for(node_set::const_iterator i = f->axioms.begin(), end = f->axioms.end(); i != end; ++i) {
      node *n = *i;
      if (hyp.implies(n->get_hypotheses()))
        try_real(n);
      else
        axioms.insert(*i);
    }
    prover.ordered_reals = f->prover.ordered_reals;
  } else prover.ordered_reals = NULL;
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i) {
    node *n = new hypothesis_node(*i);
    nodes.insert(n);
    try_real(n);
  }
}

bool graph_t::is_useful(property const &res2) const {
  node_map::const_iterator i = known_reals.find(res2.real);
  if (i != known_reals.end()) {
    property const &res1 = i->second->get_result();
    interval const &i1 = res1.bnd, &i2 = res2.bnd;
    if (i1 <= i2) return false;
  }
  return true;
}

bool graph_t::try_real(node *&n) {
  property const &res2 = n->get_result();
  node_map::iterator i = known_reals.find(res2.real);
  if (i != known_reals.end()) {
    property const &res1 = i->second->get_result();
    interval const &i1 = res1.bnd, &i2 = res2.bnd;
    if (i1 <= i2) {
      n = i->second;
      return false;
    } else if (!(i2 < i1)) {
      graph_loader loader(this);
      n = new intersection_node(i->second, n);
    }
    i->second = n;
  } else known_reals[res2.real] = n;
  return true;
}

node_vect graph_t::find_useful_axioms(ast_real const *real) {
  node_vect res;
  node_vect useless;
  for(node_set::const_iterator i = axioms.begin(), end = axioms.end(); i != end; ++i) {
    node *n = *i;
    property const &p = n->get_result();
    if (p.real == real) {
      if (is_useful(p)) res.push_back(n);
      else useless.push_back(n);
    }
  }
  for(node_vect::const_iterator i = useless.begin(), end = useless.end(); i != end; ++i)
    axioms.erase(*i);
  return res;
}

node *graph_t::find_already_known(ast_real const *real) const {
  node_map::const_iterator i = known_reals.find(real);
  return (i != known_reals.end()) ? i->second : NULL;
}

void graph_t::insert_axiom(node *n) {
  if (hyp.implies(n->get_hypotheses())) try_real(n);
  else axioms.insert(n);
}

graph_t::~graph_t() {
  for(node_set::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i)
    delete *i;
}

graph_layer::~graph_layer() {
  if (top_layer) {
    for(node_vect::const_iterator i = top_layer->begin(), end = top_layer->end(); i != end; ++i) {
      top_graph->remove(*i);
      delete *i;
    }
  }
  top_layer = old_layer;
}
