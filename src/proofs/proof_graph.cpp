#include <iostream>
#include <list>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

extern bool parameter_expensive;
extern bool parameter_constrained;

graph_t *top_graph = NULL;

unsigned visit_counter = 0;

static char *new_hyps(long &h, property_vect const &hyp) {
  unsigned nb = hyp.size();
  if (nb <= sizeof(long) * 8) {
    h = 0;
    return reinterpret_cast< char * >(&h);
  }
  char *v = new char[(nb + 7) / 8]();
  h = reinterpret_cast< long >(v);
  return v;
}

static void delete_hyps(long h, property_vect const &hyp) {
  if (hyp.size() > sizeof(long) * 8)
    delete[] reinterpret_cast< char * >(h);
}

static char *get_hyps(long &h, property_vect const &hyp) {
  if (hyp.size() > sizeof(long) * 8)
    return reinterpret_cast< char * >(h);
  else
    return reinterpret_cast< char * >(&h);
}

property_vect node::get_hypotheses() const {
  property_vect res;
  long h = get_hyps();
  if (h == 0) return res;
  property_vect const &ghyp = graph->get_hypotheses();
  char const *v = ::get_hyps(h, ghyp);
  for(unsigned i = 0, nb = ghyp.size(); i < nb; ++i)
    if (v[i / 8] & (1 << (i & 7))) res.push_back(ghyp[i]);
  return res;
}

bool node::can_visit() const {
  if (visited == visit_counter) return false;
  visited = visit_counter;
  return true;
}

typedef std::list< node * > node_list;

unsigned node::get_weight() {
  if (weight > 0) return weight;
  node_vect const &v = get_subproofs();
  weight = local_weight;
  switch (v.size()) {
  case 0: break;
  case 1: weight += v[0]->get_weight(); break;
  default:
    ++visit_counter;
    node_list pending;
    for (node_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i)
      if ((*i)->can_visit()) pending.push_back(*i);
    while (!pending.empty()) {
      node *n = pending.front();
      pending.pop_front();
      weight += n->local_weight;
      node_vect const &w = n->get_subproofs();
      for(node_vect::const_iterator i = w.begin(), end = w.end(); i != end; ++i)
        if ((*i)->can_visit()) pending.push_back(*i);
    }
  }
  return weight;
}

node_vect const &node::get_subproofs() const {
  static node_vect dummy;
  return dummy;
}

node::node(node_id t, graph_t *g)
  : type(t), graph(g), nb_good(0), nb_missing(0), visited(0), local_weight(1),
    weight(parameter_expensive ? 0 : local_weight)
{
  if (g)
    g->insert(this);
}

node::~node() {
  assert(succ.empty() && nb_good == 0);
  if (graph)
    graph->remove(this);
}

void node::remove_known() {
  assert(nb_good > 0);
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

property node::maximal() const {
  property res;
  property const &current = get_result();
  for(node_set::const_iterator i = succ.begin(), end = succ.end(); i != end; ++i) {
    property p = (*i)->maximal_for(this);
    if (res.null()) res = p;
    else res.intersect(p);
    if (!current.strict_implies(res)) break;
  }
  return res.null() ? get_result() : res;
}

static bool dominates(node const *n1, node const *n2) {
  assert(n1 && n1->graph && n2);
  return n1->graph->dominates(n2->graph);
}

theorem_node::theorem_node(int nb, property const h[], property const &p, std::string const &n, theorem_updater *u)
    : res(p), name(n), updater(u) {
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

static void fill_hyps(char *v, property_vect const &hyp, predicated_real const &r) {
  for(unsigned i = 0, nb = hyp.size(); i < nb; ++i)
    if (hyp[i].real == r)
      v[i / 8] |= 1 << (i & 7);
}

static void fill_hyps(char *v, property_vect const &hyp, node *n) {
  if (n->type == HYPOTHESIS) {
    fill_hyps(v, hyp, n->get_result().real);
    return;
  }
  property_vect const &nhyp = n->graph->get_hypotheses();
  long h = n->get_hyps();
  char const *nv = get_hyps(h, nhyp);
  unsigned nb = nhyp.size();
  if (&hyp == &nhyp)
    for(unsigned i = 0, end = (nb + 7) / 8; i < end; ++i) v[i] |= nv[i];
  else
    for(unsigned i = 0; i < nb; ++i)
      if (nv[i / 8] & (1 << (i & 7))) fill_hyps(v, hyp, nhyp[i].real);
}

modus_node::modus_node(theorem_node *n)
    : dependent_node(MODUS) {
  assert(n);
  target = n;
  if (n->name == "$FALSE")
  {
    assert(!parameter_constrained && n->hyp.size() == 0);
    nb_missing = 1;
    return;
  }
  int missing = 0;
  property_vect const &ghyp = graph->get_hypotheses();
  char *v = new_hyps(hyps, ghyp);
  node_set nodes;
  for (property_vect::const_iterator i = n->hyp.begin(),
       i_end = n->hyp.end(); i != i_end; ++i)
  {
    node *m = find_proof(*i);
    if (!m)
    {
      assert(!parameter_constrained);
      m = create_theorem(0, NULL, *i, "$FALSE");
    }
    assert(m && dominates(m, this));
    fill_hyps(v, ghyp, m);
    if (m->type != HYPOTHESIS && nodes.insert(m).second)
      insert_pred(m);
    if (m->nb_missing)
    {
      assert(!parameter_constrained);
      ++missing;
      if (m->nb_missing > nb_missing)
        nb_missing = m->nb_missing;
    }
  }
  nb_missing += missing;
}

modus_node::~modus_node() {
  // axioms are not owned by modus node
  if (!target->name.empty())
    delete target;
  delete_hyps(hyps, graph->get_hypotheses());
}

property modus_node::maximal_for(node const *n) const {
  if (!target->updater) return n->get_result();
  predicated_real r = n->get_result().real;
  property res;
  for(property_vect::const_iterator i = target->hyp.begin(),
      end = target->hyp.end(); i != end; ++i) {
    if (r != i->real) continue;
    if (res.null()) res = *i;
    else res.intersect(*i);
  }
  assert(!res.null());
  return res;
}

void modus_node::enlarge(property const &p) {
  if (!target->updater) return;
  target->updater->expand(target, p);
}

node *create_theorem(int nb, property const h[], property const &p, std::string const &n, theorem_updater *u) {
  return new modus_node(new theorem_node(nb, h, p, n, u));
}

class intersection_node: public dependent_node {
  property res;
  long hyps;
 public:
  intersection_node(node *n1, node *n2);
  ~intersection_node() { delete_hyps(hyps, graph->get_hypotheses()); }
  virtual property const &get_result() const { return res; }
  virtual long get_hyps() const { return hyps; }
  virtual property maximal() const { return res.null() ? res : node::maximal(); }
  virtual property maximal_for(node const *) const;
  virtual void enlarge(property const &p) { res = p; }
};

intersection_node::intersection_node(node *n1, node *n2)
    : dependent_node(INTERSECTION) {
  assert(dominates(n1, this) && dominates(n2, this));
  property const &res1 = n1->get_result(), &res2 = n2->get_result();
  assert(res1.real == res2.real && res1.real.pred_bnd());
  res = res1;
  res.intersect(res2);
  if (lower(res1.bnd()) > lower(res2.bnd())) std::swap(n1, n2);
  // to simplify the graph, no intersection should be nested
  if (n1->type == INTERSECTION) n1 = n1->get_subproofs()[0];
  if (n2->type == INTERSECTION) n2 = n2->get_subproofs()[1];
  // by disallowing both nodes to be hypotheses, we are sure that even if the
  // output real is also an input, it is a meaningful input; enforced by the parser
  assert(n1->type != HYPOTHESIS || n2->type != HYPOTHESIS);
  insert_pred(n1);
  insert_pred(n2);
  property_vect const &ghyp = graph->get_hypotheses();
  char *v = new_hyps(hyps, ghyp);
  fill_hyps(v, ghyp, n1);
  fill_hyps(v, ghyp, n2);
  if (is_empty(res.bnd())) {
    res = property();
    top_graph->set_contradiction(this);
  }
}

property intersection_node::maximal_for(node const *n) const {
  node_vect const &v = get_subproofs();
  number l = number::neg_inf, u = number::pos_inf;
  if (res.null()) {
    // TODO: improve bounds
    if (n == v[0]) u = upper(v[0]->get_result().bnd());
    else l = lower(v[1]->get_result().bnd());
  } else {
    if (n == v[0])
      u = upper(res.bnd());
    else
      l = lower(res.bnd());
  }
  return property(n->get_result().real, interval(l, u));
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
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i) {
    interval const &bnd = i->bnd();
    if (!is_bounded(bnd)) {
      if (known_reals.count(i->real) == 0)
        partial_reals.insert(std::make_pair(i->real, new hypothesis_node(*i)));
    } else try_real(new hypothesis_node(*i));
  }
}

void graph_t::purge() {
  for(node_map::const_iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
    i->second->remove_known();
  for(node_map::const_iterator i = partial_reals.begin(), end = partial_reals.end(); i != end; ++i)
    delete i->second;
  known_reals.clear();
  partial_reals.clear();
}

void graph_t::set_contradiction(node *n) {
  assert(n && !contradiction);
  contradiction = n;
  ++n->nb_good;
  purge();
}

int stat_successful_th = 0, stat_discarded_pred = 0, stat_intersected_pred = 0;

bool graph_t::try_real(node *n) {
  assert(top_graph == this && !contradiction);
  assert(n && n->graph && n->graph->dominates(this));
  property const &res2 = n->get_result();
  ++stat_successful_th;
  std::pair< node_map::iterator, bool > ib = known_reals.insert(std::make_pair(res2.real, n));
  node *&dst = ib.first->second;
  if (!ib.second) { // there was already a known range
    node *old = dst;
    property const &res1 = old->get_result();
    if (res1.strict_implies(res2)) {
      ++stat_discarded_pred;
      delete n;
      return false;
    }
    if (res1.implies(res2)) {
      if (n->get_weight() >= old->get_weight() ||
          n->nb_missing >= old->nb_missing)
      {
        ++stat_discarded_pred;
        delete n;
        return false;
      }
    } else if (!res2.strict_implies(res1)) {
      ++stat_intersected_pred;
      n = new intersection_node(old, n);
      if (n == contradiction) return true;
    }
    dst = n;
    old->remove_known();
  } else {
    node_map::iterator i = partial_reals.find(res2.real);
    if (i != partial_reals.end()) { // there is a known inequality
      node *m = i->second;
      partial_reals.erase(i);
      property const &res1 = m->get_result();
      if (!res2.implies(res1)) {
        node *old = n;
        ++n->nb_good; // n has just become a known real, this data is needed in case a contradiction is found
        n = new intersection_node(n, m);
        if (n == contradiction) return true;
        dst = n;
        --old->nb_good;
      } else delete m;
    }
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
  } else purge();
  assert(nodes.empty());
}

void graph_t::replace_known(node_vect const &v) {
  node_map old;
  old.swap(known_reals);
  for(node_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    node *n = *i;
    ++n->nb_good;
    known_reals.insert(std::make_pair(n->get_result().real, n));
  }
  for(node_map::const_iterator i = old.begin(), end = old.end(); i != end; ++i)
    i->second->remove_known();
  for(node_map::const_iterator i = partial_reals.begin(), end = partial_reals.end(); i != end; ++i)
    delete i->second;
  partial_reals.clear();
}

void graph_t::show_dangling() const
{
  bool first = true;
  for (node_set::const_iterator i = nodes.begin(), i_end = nodes.end(); i != i_end; ++i)
  {
    node *n = *i;
    if (n->type == MODUS && static_cast< modus_node * >(n)->target->name == "$FALSE")
    {
      if (first)
      {
        first = false;
        std::cerr << "Unproven assumptions:\n";
      }
      std::cerr << "  " << dump_property(n->get_result()) << '\n';
    }
  }
}

void enlarger(node_vect const &nodes) {
  ++visit_counter;
  node_list pending;
  for (node_vect::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i)
    if ((*i)->can_visit()) pending.push_back(*i);
  for (node_list::iterator i = pending.begin(); i != pending.end(); ++i) {
    node_vect const &v = (*i)->get_subproofs();
    for(node_vect::const_iterator j = v.begin(), end = v.end(); j != end; ++j)
      if ((*j)->can_visit()) pending.push_back(*j);
  }
  while (!pending.empty()) {
    node *n = pending.front();
    pending.pop_front();
    n->visited = 0;
    property old_res = n->get_result();
    if (old_res.null()) continue;
    property max_res = n->maximal();
    if (!old_res.strict_implies(max_res)) continue;
    n->enlarge(max_res);
    if (!old_res.strict_implies(n->get_result())) continue;
    node_vect const &v = n->get_subproofs();
    for(node_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i)
      if ((*i)->can_visit()) pending.push_back(*i);
  }
}
