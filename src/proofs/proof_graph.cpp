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

node::node(node_id t, graph_t *g): type(t), graph(g) {
  if (g)
    g->insert(this);
}

node::~node() {
  assert(succ.empty());
  graph->remove(this);
}

bool graph_t::dominates(graph_t const *g) const {
  while (g) {
    if (g == this) return true;
    g = g->father;
  }
  return false;
}

static bool dominates(node const *n1, node const *n2) {
  assert(n1);
  if (n1->type == AXIOM) return true;
  assert(n1->graph && n2);
  return n1->graph->dominates(n2->graph);
}

result_node::result_node(node_id t, property const &p, graph_t *g): node(t, g), res(p) {}

theorem_node::theorem_node(int nb, property const h[], property const &p, std::string const &n)
    : result_node(THEOREM, p), name(n) {
  for(int i = 0; i < nb; ++i) hyp.push_back(h[i]);
}

void dependent_node::insert_pred(node *n) {
  assert(dominates(n, this) || type == UNION);
  n->succ.insert(this);
  pred.push_back(n);
}

void dependent_node::clean_dependencies() {
  for(node_vect::const_iterator i = pred.begin(), end = pred.end(); i != end; ++i) {
    node *n = *i;
    n->succ.erase(this);
  }
  pred.clear();
}

dependent_node::~dependent_node() {
  clean_dependencies();
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
  assert(dominates(n, this) && n->type != INTERSECTION);
  insert_pred(n);
  property_map pmap, rmap;
  for(int i = 0; i < nb; ++i) {
    node *m = nodes[i];
    assert(dominates(m, this));
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
  assert(dominates(n1, this) && dominates(n2, this));
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

class graph_node: public node {
  graph_node(graph_t *g): node(GRAPH, NULL) { graph = g; }
  friend class graph_t;
 public:
  virtual property const &get_result() const { assert(false); }
  virtual property_vect const &get_hypotheses() const { assert(false); }
  virtual node_vect const &get_subproofs() const;
};

node_vect const &graph_node::get_subproofs() const {
  static node_vect plouf;
  plouf.clear();
  node_map const &m = graph->known_reals;
  for(node_map::const_iterator i = m.begin(), end = m.end(); i != end; ++i)
    plouf.push_back(i->second);
  return plouf;
}

graph_t::graph_t(graph_t *f, property_vect const &h)
  : father(f), known_node(new graph_node(this)), hyp(h) {
  graph_loader loader(this);
  if (f) {
    assert(hyp.implies(f->hyp));
    known_reals = f->known_reals;
    for(node_set::const_iterator i = f->axioms.begin(), end = f->axioms.end(); i != end; ++i)
      insert_axiom(*i);
    prover.helper = duplicate_proof_helper(f->prover.helper);
  } else prover.helper = NULL;
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i) {
    node *n = new hypothesis_node(*i);
    if (!try_real(n))
      delete n;
  }
}

ast_real_vect graph_t::get_known_reals() const {
  ast_real_vect res(known_reals.size());
  for(node_map::const_iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
    res.push_back(i->first);
  return res;
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

bool graph_t::try_real(node *n) {
  assert(n && n->graph && n->graph->dominates(this));
  property const &res2 = n->get_result();
  std::pair< node_map::iterator, bool > ib = known_reals.insert(std::make_pair(res2.real, n));
  node *&dst = ib.first->second;
  if (!ib.second) { // there was already a known real
    node *old = dst;
    property const &res1 = old->get_result();
    interval const &i1 = res1.bnd, &i2 = res2.bnd;
    if (i1 <= i2)
      return false;
    else if (!(i2 < i1)) {
      graph_loader loader(this);
      n = new intersection_node(old, n);
    }
    dst = n;
    old->succ.erase(known_node);
  }
  n->succ.insert(known_node);
  return true;
}

node_vect graph_t::find_useful_axioms(ast_real const *real) {
  node_vect res;
  node_set ax;
  ax.swap(axioms);
  for(node_set::const_iterator i = ax.begin(), end = ax.end(); i != end; ++i) {
    node *n = *i;
    property const &p = n->get_result();
    if (p.real == real)
      if (is_useful(p)) {
        res.push_back(n);
        axioms.insert(n);
      }
    else axioms.insert(n);
  }
  return res;
}

node *graph_t::find_already_known(ast_real const *real) const {
  node_map::const_iterator i = known_reals.find(real);
  return (i != known_reals.end()) ? i->second : NULL;
}

void graph_t::insert_axiom(node *n) {
  assert(n && n->type == AXIOM && !n->graph);
  if (hyp.implies(n->get_hypotheses())) {
    graph_loader loader(this);
    node *m = new modus_node(0, NULL, n);
    if (!try_real(m))
      delete m;
  } else axioms.insert(n);
}

graph_t::~graph_t() {
  for(node_set::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i) {
    node *n = *i;
    assert(n && n->graph == this);
    n->clean_dependencies();
  }
  for(node_map::const_iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i) {
    node *n = i->second;
    n->succ.erase(known_node);
  }
  node_set ns;
  ns.swap(nodes);
  for(node_set::const_iterator i = ns.begin(), end = ns.end(); i != end; ++i)
    delete *i;
  delete_proof_helper(prover.helper);
  delete known_node;
}

void graph_t::flatten() {
  assert(father && father->hyp.implies(hyp));
  node_set ns;
  ns.swap(nodes);
  for(node_set::const_iterator i = ns.begin(), end = ns.end(); i != end; ++i) {
    node *n = *i;
    assert(n && n->graph == this);
    if (n->type != HYPOTHESIS) {
      father->nodes.insert(n);
      n->graph = father;
    } else nodes.insert(n);
  }
  for(node_map::const_iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
    father->try_real(i->second);
}

void graph_t::purge(node *except) {
  std::set< ast_real const * > reals;
  for(property_vect::const_iterator i = prover.goals.begin(), i_end = prover.goals.end(); i != i_end; ++i)
    reals.insert(i->real);
  node_map m;
  m.swap(known_reals);
  for(node_map::const_iterator i = m.begin(), i_end = m.end(); i != i_end; ++i) {
    if (reals.count(i->first) == 0)
      i->second->succ.erase(known_node);
    else
      known_reals.insert(*i);
  }
  node_set ns(nodes);
  while (!ns.empty()) {
    node *n = *ns.begin();
    ns.erase(n);
    if (n == except || n->graph != this || !n->succ.empty() || n->type == GRAPH) continue;
    node_vect const &v = n->get_subproofs();
    ns.insert(v.begin(), v.end());
    delete n;
  }
}

void graph_t::migrate() {
  assert(father);
  node_set ns(nodes);
  while (!ns.empty()) {
    node *n = *ns.begin();
    ns.erase(n);
    if (n->graph != this || n->type == HYPOTHESIS || n->type == GRAPH) continue;
    node_vect const &v = n->get_subproofs();
    bool good = true;
    for(node_vect::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
      if (::dominates(n, *i)) {
        good = false;
        break;
      }
    if (!good || !father->hyp.implies(n->get_hypotheses())) continue;
    nodes.erase(n);
    father->nodes.insert(n);
    n->graph = father;
    father->try_real(n);
    ns.insert(n->succ.begin(), n->succ.end());
  }
}
