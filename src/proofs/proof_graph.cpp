#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

graph_t *top_graph = NULL;

property_vect const &node::get_hypotheses() const {
  static property_vect dummy;
  return dummy;
}

node_vect const &node::get_subproofs() const {
  static node_vect dummy;
  return dummy;
}

node::node(node_id t, graph_t *g): type(t), graph(g), nb_good(0) {
  if (g)
    g->insert(this);
}

node::~node() {
  assert(succ.empty() && nb_good == 0);
  if (graph)
    graph->remove(this);
}

void node::remove_known() {
  if (--nb_good == 0 && succ.empty()) delete this;
}

void node::remove_succ(node const *n) {
  succ.erase(const_cast< node * >(n));
  if (succ.empty() && nb_good == 0) delete this;
}

bool graph_t::dominates(graph_t const *g) const {
  while (g) {
    if (g == this) return true;
    g = g->father;
  }
  return false;
}

static bool dominates(node const *n1, node const *n2) {
  assert(n1 && n1->graph && n2);
  return n1->graph->dominates(n2->graph);
}

theorem_node::theorem_node(int nb, property const h[], property const &p, std::string const &n)
    : res(p), name(n) {
  for(int i = 0; i < nb; ++i) hyp.push_back(h[i]);
}

void dependent_node::insert_pred(node *n) {
  assert(dominates(n, this) || type == UNION);
  n->succ.insert(this);
  pred.push_back(n);
}

void dependent_node::clean_dependencies() {
  std::sort(pred.begin(), pred.end()); // do not remove a node more than once
  for(node_vect::const_iterator i = pred.begin(), end = std::unique(pred.begin(), pred.end()); i != end; ++i)
    (*i)->remove_succ(this);
  pred.clear();
}

typedef std::map< predicated_real, property > property_map;

// intersecting shouldn't create a wrong proof: by design
// (for an hypothesis map) - the hypotheses are all satisfiable, hence their intersection too
// (for a result map) - the results have been generated at the same time, they are identical
static void fill_property_map(property_map &m, property const &p) {
  std::pair< property_map::iterator, bool > pki = m.insert(std::make_pair(p.real, p));
  if (!pki.second) // there was already a similar predicate
    pki.first->second.intersect(p);
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
    v.push_back(i->second);
}

modus_node::modus_node(theorem_node *n)
    : dependent_node(MODUS) {
  assert(n);
  target = n;
  property_map pmap;
  for(property_vect::const_iterator i = n->hyp.begin(), i_end = n->hyp.end();
      i != i_end; ++i) {
    node *m = find_proof(*i);
    assert(m && dominates(m, this));
    fill_property_map(pmap, m);
    if (m->type != HYPOTHESIS)
      insert_pred(m);
  }
  fill_property_vect(hyp, pmap);
}

modus_node::~modus_node() {
  // axioms are not owned by modus node
  if (!target->name.empty())
    delete target;
}

node *create_theorem(int nb, property const h[], property const &p, std::string const &n) {
  return new modus_node(new theorem_node(nb, h, p, n));
}

class intersection_node: public dependent_node {
  property res;
  property_vect hyp;
 public:
  intersection_node(node *n1, node *n2);
  virtual property const &get_result() const { return res; }
  virtual property_vect const &get_hypotheses() const { return hyp; }
};

intersection_node::intersection_node(node *n1, node *n2)
    : dependent_node(INTERSECTION) {
  assert(dominates(n1, this) && dominates(n2, this));
  property const &res1 = n1->get_result(), &res2 = n2->get_result();
  assert(res1.real == res2.real);
  res = res1;
  res.intersect(res2);
  if (res.real.pred() == PRED_BND && lower(res1.bnd()) > lower(res2.bnd())) std::swap(n1, n2);
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
  if (res.real.pred() == PRED_BND && is_empty(res.bnd())) {
    res = property();
    top_graph->set_contradiction(this);
  }
}

graph_t::graph_t(graph_t *f, property_vect const &h)
  : father(f), hyp(h), contradiction(NULL) {
  graph_loader loader(this);
  if (f) {
    assert(hyp.implies(f->hyp));
    assert(!f->contradiction);
    known_reals = f->known_reals;
    for(node_map::iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
      ++i->second->nb_good;
  }
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
    try_real(new hypothesis_node(*i));
}

void graph_t::set_contradiction(node *n) {
  assert(n);
  contradiction = n;
  ++n->nb_good;
  for(node_map::const_iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
    i->second->remove_known();
  known_reals.clear();
}

bool graph_t::try_real(node *n) {
  assert(top_graph == this);
  assert(n && n->graph && n->graph->dominates(this));
  property const &res2 = n->get_result();
  std::pair< node_map::iterator, bool > ib = known_reals.insert(std::make_pair(res2.real, n));
  node *&dst = ib.first->second;
  if (!ib.second) { // there was already a known real
    node *old = dst;
    property const &res1 = old->get_result();
    if (res1.implies(res2)) {
      delete n;
      return false;
    } else if (!res2.strict_implies(res1)) {
      n = new intersection_node(old, n);
      if (n == contradiction) return true;
    }
    dst = n;
    old->remove_known();
  }
  ++n->nb_good;
  return true;
}

node *graph_t::find_already_known(predicated_real const &real) const {
  node_map::const_iterator i = known_reals.find(real);
  return (i != known_reals.end()) ? i->second : NULL;
}

graph_t::~graph_t() {
  if (contradiction) {
    --contradiction->nb_good;
    delete contradiction;
  } else
    for(node_map::const_iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
      i->second->remove_known();
  assert(nodes.empty());
}
