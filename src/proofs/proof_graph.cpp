#include "numbers/interval_utility.hpp"
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

modus_node::modus_node(int nb, node *nodes[], node *n)
    : dependent_node(MODUS, n->get_result()) {
  insert_pred(n);
  typedef std::map< ast_real const *, interval > property_map;
  property_map pmap, rmap;
  for(int i = 0; i < nb; ++i) {
    node *m = nodes[i];
    if (m->type == HYPOTHESIS) continue;
    insert_pred(m);
    {
      property const &p = m->get_result();
      property_map::iterator pki = rmap.find(p.real);
      if (pki != rmap.end())
        pki->second = intersect(pki->second, p.bnd);
      else
        rmap.insert(std::make_pair(p.real, p.bnd));
    }
    property_vect const &m_hyp = m->get_hypotheses();
    for(property_vect::const_iterator j = m_hyp.begin(), j_end = m_hyp.end(); j != j_end; ++j) {
      property const &p = *j;
      property_map::iterator pki = pmap.find(p.real);
      if (pki != pmap.end())
        pki->second = hull(pki->second, p.bnd);
      else
        pmap.insert(std::make_pair(p.real, p.bnd));
    }
  }
  property_vect const &n_hyp = n->get_hypotheses();
  for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end(); j != j_end; ++j) {
    property const &p = *j;
    property_map::iterator pki = rmap.find(p.real); // is the hypothesis a result?
    if (pki != rmap.end() && pki->second <= p.bnd) continue;
    pki = pmap.find(p.real);
    if (pki != pmap.end())
      pki->second = hull(pki->second, p.bnd);
    else
      pmap.insert(std::make_pair(p.real, p.bnd));
  }
  for(property_map::const_iterator pki = pmap.begin(), pki_end = pmap.end(); pki != pki_end; ++pki) {
    property p(pki->first, pki->second);
    hyp.push_back(p);
  }
}

graph_t::graph_t(graph_t *f, property_vect const &h): father(f), hyp(h) {
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i) {
    node *n = new hypothesis_node(*i);
    nodes.insert(n);
    try_real(n);
  }
  if (!f) return;
  assert(hyp.implies(f->hyp));
  for(node_set::const_iterator i = f->nodes.begin(), end = f->nodes.end(); i != end; ++i) {
    node *n = *i;
    hyp.implies(n->get_hypotheses()) && try_real(n);
  }
}

bool graph_t::test_real(property const &res2) const {
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
      interval i0 = intersect(i1, i2);
      property res(res2.real, i0);
      node *ns[2] = { i->second, n };
      property hyps[2] = { res1, res2 };
      assert(top_graph == this);
      n = new modus_node(2, ns, new theorem_node(2, hyps, res, "intersect"));
    }
    i->second = n;
  } else known_reals[res2.real] = n;
  return true;
}

node_vect graph_t::find_good_axioms(ast_real const *real) const {
  node_vect res;
  for(node_set::const_iterator i = axioms.begin(), end = axioms.end(); i != end; ++i) {
    node *n = *i;
    property const &p = n->get_result();
    if (p.real == real && test_real(p)) res.push_back(n);
  }
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
