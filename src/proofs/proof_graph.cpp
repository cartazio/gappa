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
  if (graph)
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

modus_node::modus_node(property_vect const &h, node_vect const &nodes, node *n)
    : dependent_node(MODUS, n->get_result()) {
  target = n;
  for(node_vect::const_iterator i = nodes.begin(), i_end = nodes.end();
      i != i_end; ++i) {
    node *m = *i;
    assert(dominates(m, this) && m->type != HYPOTHESIS);
    insert_pred(m);
  }
  hyp = h;
}

modus_node::~modus_node() {
  if (target->type != AXIOM)
    delete target;
}

// a modus can only target an axiom, a theorem, or an union; unless it is an
// axiom, the target will be strictly owned by the modus

node *create_modus(node *n) {
  assert(n->type == THEOREM || n->type == AXIOM || n->type == UNION);
  assert(n->type == AXIOM || n->succ.empty());
  typedef std::set< ast_real const * > real_set;
  node_vect nodes;
  real_set reals;
  property_vect const &n_hyp = n->get_hypotheses();
  for(property_vect::const_iterator i = n_hyp.begin(), i_end = n_hyp.end();
      i != i_end; ++i) {
    node *m = find_proof(*i);
    assert(m);
    if (m->type == HYPOTHESIS)
      reals.insert(i->real);
    else {
      property_vect const &m_hyp = m->get_hypotheses();
      for(property_vect::const_iterator j = m_hyp.begin(), j_end = m_hyp.end();
          j != j_end; ++j)
        reals.insert(j->real);
      nodes.push_back(m);
    }
  }
  if (n->type == UNION && nodes.empty())
    return n;
  property_vect hyp;
  for(real_set::const_iterator i = reals.begin(), i_end = reals.end();
      i != i_end; ++i) {
    node *m = find_proof(*i);
    assert(m);
    hyp.push_back(m->get_result());
  }
  if (n->type != AXIOM) {
    n->graph->remove(n);
    n->graph = NULL;
  }
  node *res = new modus_node(hyp, nodes, n);
  if (n->type == AXIOM)
    n->succ.insert(res);
  return res;
}

node *create_theorem(int nb, property const h[], property const &p, std::string const &n) {
  return create_modus(new theorem_node(nb, h, p, n));
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
  if (is_empty(get_result().bnd))
    top_graph->contradiction = this;
}

class graph_node: public node {
  graph_node(graph_t *g): node(GRAPH, NULL) { graph = g; }
  friend class graph_t;
 public:
  virtual property const &get_result() const { assert(false); }
  virtual property_vect const &get_hypotheses() const { assert(false); }
  virtual node_vect const &get_subproofs() const {assert(false); }
};

static void delete_forest(node_set &nodes, node *except) {
  while (!nodes.empty()) {
    node *n = *nodes.begin();
    nodes.erase(n);
    if (n == except || !n->succ.empty()) continue;
    if (n->type != UNION) {
      node_vect const &v = n->get_subproofs();
      nodes.insert(v.begin(), v.end());
    }
    delete n;
  }
}

static void delete_tree(node *n) {
  node_set ns;
  ns.insert(n);
  delete_forest(ns, NULL);
}

graph_t::graph_t(graph_t *f, property_vect const &h, property_vect const &g, proof_helper *p, bool o)
  : father(f), known_node(new graph_node(this)), hyp(h), goals(g),
    owned_helper(o), contradiction(NULL) {
  graph_loader loader(this);
  if (f) {
    assert(hyp.implies(f->hyp));
    known_reals = f->known_reals;
    for(node_set::const_iterator i = f->axioms.begin(), end = f->axioms.end(); i != end; ++i)
      insert_axiom(*i);
  }
  if (owned_helper) helper = duplicate_proof_helper(p);
  else helper = p;
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
    try_real(new hypothesis_node(*i));
}

ast_real_vect graph_t::get_known_reals() const {
  ast_real_vect res(known_reals.size());
  for(node_map::const_iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
    res.push_back(i->first);
  return res;
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
    delete_tree(old);
  }
  n->succ.insert(known_node);
  return true;
}

node_vect graph_t::find_useful_axioms(ast_real const *real) {
  node_vect res;
  node_set ax;
  ax.swap(axioms);
  node_map::const_iterator j_end = known_reals.end();
  for(node_set::const_iterator i = ax.begin(), i_end = ax.end(); i != i_end; ++i) {
    node *n = *i;
    property const &p = n->get_result();
    if (p.real == real) {
      node_map::const_iterator j = known_reals.find(real);
      if (j != j_end) {
        interval const &i1 = j->second->get_result().bnd, &i2 = p.bnd;
        if (i1 <= i2) continue;
      }
      res.push_back(n);
    }
    axioms.insert(n);
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
    try_real(create_modus(n));
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
  if (owned_helper)
    delete_proof_helper(helper);
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
  for(property_vect::const_iterator i = goals.begin(), i_end = goals.end(); i != i_end; ++i)
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
  delete_forest(ns, except);
}

bool graph_t::migrate() {
  bool res = false;
  assert(father);
  node_set ns(nodes);
  while (!ns.empty()) {
    node *n = *ns.begin();
    ns.erase(n);
    if (n->graph != this || n->type == HYPOTHESIS || n->type == GRAPH) continue;
    node_vect const &v = n->get_subproofs();
    bool good = true;
    for(node_vect::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
      if (!(*i)->graph->dominates(father)) {
        good = false;
        break;
      }
    if (!good || !father->hyp.implies(n->get_hypotheses())) continue;
    nodes.erase(n);
    father->nodes.insert(n);
    n->graph = father;
    ns.insert(n->succ.begin(), n->succ.end());
    father->try_real(n);
    res = true;
  }
  return res;
}
