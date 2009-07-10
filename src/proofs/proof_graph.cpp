#include <iostream>
#include <list>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"
#include "proofs/updater.hpp"

extern bool parameter_expensive;
extern bool parameter_constrained;

graph_t *top_graph = NULL;

/** Timestamp for the currently running graph algorithm. Increased each time an algorithm starts. */
static unsigned visit_counter = 0;

/**
 * Creates a bit vector representing the empty subset for the properties of \a hyp.
 * If the bit vector fits inside a pointer word, it is stored directly. Otherwise a pointer to it is used.
 * The indirection is seldom used, as propositions usually have less than 32/64 global hypotheses.
 * @param h   A reference to the data to be stored, either the bit vector or a pointer to it.
 * @param hyp A vector of properties. The same vector should then be passed to the functions ::get_hyps and ::delete_hyps.
 * @return A pointer to the bit vector.
 */
static char *new_hyps(long &h, property_vect const &hyp)
{
  unsigned nb = hyp.size();
  if (nb <= sizeof(long) * 8)
  {
    h = 0;
    return reinterpret_cast< char * >(&h);
  }
  char *v = new char[(nb + 7) / 8]();
  h = reinterpret_cast< long >(v);
  return v;
}

/**
 * Deletes a compressed property_vect.
 * @see ::new_hyps
 */
static void delete_hyps(long h, property_vect const &hyp)
{
  if (hyp.size() > sizeof(long) * 8)
    delete[] reinterpret_cast< char * >(h);
}

/**
 * Returns a pointer to the bit vector representing a compressed property_vect.
 * @see ::new_hyps
 */
static char *get_hyps(long &h, property_vect const &hyp)
{
  if (hyp.size() > sizeof(long) * 8)
    return reinterpret_cast< char * >(h);
  else
    return reinterpret_cast< char * >(&h);
}

/**
 * Uncompresses the vector of global hypotheses this node (in)directly depends on.
 * The carrier vector is the hypotheses of the graph that owns this node.
 */
property_vect node::get_hypotheses() const
{
  property_vect res;
  long h = get_hyps();
  if (h == 0) return res;
  property_vect const &ghyp = graph->get_hypotheses();
  char const *v = ::get_hyps(h, ghyp);
  for (unsigned i = 0, nb = ghyp.size(); i < nb; ++i)
    if (v[i / 8] & (1 << (i & 7))) res.push_back(ghyp[i]);
  return res;
}

/**
 * Tells if the node has yet to be visited by the current graph algorithm.
 * In that case, the function updates the #visited timestamp so that the next call returns false.
 */
bool node::can_visit() const
{
  if (visited == visit_counter) return false;
  visited = visit_counter;
  return true;
}

typedef std::list< node * > node_list;

/**
 * Computes the sum of the #local_weight of all the ancestors of this node.
 * The result is cached in the #weight data member.
 * @note Outside the expensive mode, the weights of the nodes are their #local_weight.
 */
unsigned node::get_weight()
{
  if (weight > 0) return weight;
  node_vect const &v = get_subproofs();
  weight = local_weight;
  switch (v.size())
  {
    case 0:
      break;
    case 1:
      weight += v[0]->get_weight();
      break;
    default:
      ++visit_counter;
      node_list pending;
      for (node_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i)
        if ((*i)->can_visit()) pending.push_back(*i);
      while (!pending.empty())
      {
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

/**
 * Returns the immediate ancestors of this node.
 * By default, a node has no ancestors.
 */
node_vect const &node::get_subproofs() const
{
  static node_vect dummy;
  return dummy;
}

/**
 * Creates a node of type @a t. Inserts it in the graph @a g, if any.
 */
node::node(node_id t, graph_t *g)
  : type(t), graph(g), nb_good(0), nb_missing(0), visited(0), local_weight(1),
    weight(parameter_expensive ? 0 : local_weight)
{
  if (g)
    g->insert(this);
}

/**
 * Destroys the node and removes from its graph #graph.
 * @pre The graph should have no successors nor be referenced by any graph_t::known_reals.
 */
node::~node()
{
  assert(succ.empty() && nb_good == 0);
  if (graph)
    graph->remove(this);
}

/**
 * Called when this node is removed from a graph_t::known_reals.
 * Automatically destroys this node if possible.
 */
void node::remove_known()
{
  assert(nb_good > 0);
  if (--nb_good == 0 && succ.empty()) delete this;
}

/**
 * Removes the node @a n from the successors of this node.
 * Automatically destroys this node if possible
 */
void node::remove_succ(node const *n)
{
  succ.erase(const_cast< node * >(n));
  if (succ.empty() && nb_good == 0) delete this;
}

/**
 * Tells if the graph @a g is a super-set of this graph.
 * @note It means that @a g has weaker hypotheses than this graph.
 */
bool graph_t::dominates(graph_t const *g) const
{
  while (g)
  {
    if (g == this) return true;
    g = g->father;
  }
  return false;
}

/**
 * Returns the widest property this node can prove without invalidating one of the successors.
 */
property node::maximal() const
{
  property res;
  property const &current = get_result();
  for(node_set::const_iterator i = succ.begin(), end = succ.end(); i != end; ++i)
  {
    property p = (*i)->maximal_for(this);
    if (res.null()) res = p;
    else res.intersect(p);
    if (!current.strict_implies(res)) break;
  }
  return res.null() ? get_result() : res;
}

/**
 * Tells if the node @a n1 is owned by a graph dominating the graph of the node @a n2.
 * @note It means that @a n2 can rely on the result proven by @a n1.
 * @see graph_t::dominates
 */
static bool dominates(node const *n1, node const *n2)
{
  assert(n1 && n1->graph && n2);
  return n1->graph->dominates(n2->graph);
}

theorem_node::theorem_node(int nb, property const h[], property const &p, std::string const &n, theorem_updater *u)
  : res(p), name(n), updater(u)
{
  for(int i = 0; i < nb; ++i) hyp.push_back(h[i]);
}

/**
 * Adds the node @a n as an immediate ancestor to this node.
 * @pre If this node is not an ::UNION node, then the node @a n shall dominate it.
 */
void dependent_node::insert_pred(node *n) {
  assert(dominates(n, this) || type == UNION);
  n->succ.insert(this);
  pred.push_back(n);
}

/**
 * Removes all the dependencies of this node.
 * @note As the node is no longer a successor of the nodes it immediatly relies on, this may cause these nodes to be collected.
 */
void dependent_node::clean_dependencies()
{
  std::sort(pred.begin(), pred.end()); // do not remove a node more than once
  for(node_vect::const_iterator i = pred.begin(), end = std::unique(pred.begin(), pred.end()); i != end; ++i)
    (*i)->remove_succ(this);
  pred.clear();
}

/**
 * Marks all the hypotheses about @a r, in the compressed property_vect represented by the bit vector @a v.
 */
static void fill_hyps(char *v, property_vect const &hyp, predicated_real const &r)
{
  for(unsigned i = 0, nb = hyp.size(); i < nb; ++i)
    if (hyp[i].real == r)
      v[i / 8] |= 1 << (i & 7);
}

/**
 * Marks all the hypotheses used by the node @a n, in the compressed property_vect represented by the bit vector @a v.
 * @note While a ::HYPOTHESIS node does not really rely on any hypothesis, it still adds itself to @a v.
 */
static void fill_hyps(char *v, property_vect const &hyp, node *n)
{
  if (n->type == HYPOTHESIS)
  {
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

/**
 * Creates a ::MODUS node. Finds predecessors needed by @a n with ::find_proof.
 * Merges the global hypotheses of predecessors to obtain the global hypotheses of this node.
 */
modus_node::modus_node(theorem_node *n)
  : dependent_node(MODUS)
{
  assert(n);
  target = n;
  if (n->name == "$FALSE")
  {
    assert(!parameter_constrained);
    nb_missing = 1 + n->hyp.size();
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

modus_node::~modus_node()
{
  // axioms are not owned by modus node
  if (!target->name.empty())
    delete target;
  delete_hyps(hyps, graph->get_hypotheses());
}

/**
 * Returns the intersection of all the hypotheses dealing with the same real than the result proved by @a n.
 * @note If the #target theorem has no updater, the hypotheses have not changed creation time.
 *       So the intersection can be skipped since it will not produce a wider result.
 */
property modus_node::maximal_for(node const *n) const
{
  if (!target->updater) return n->get_result();
  predicated_real r = n->get_result().real;
  property res;
  for (property_vect::const_iterator i = target->hyp.begin(),
       end = target->hyp.end(); i != end; ++i)
  {
    if (r != i->real) continue;
    if (res.null()) res = *i;
    else res.intersect(*i);
  }
  assert(!res.null());
  return res;
}

void modus_node::enlarge(property const &p)
{
  if (!target->updater) return;
  target->updater->expand(target, p);
}

/** Helper function for creating both a ::MODUS node and its associated ::theorem_node. */
node *create_theorem(int nb, property const h[], property const &p, std::string const &n, theorem_updater *u)
{
  return new modus_node(new theorem_node(nb, h, p, n, u));
}

class intersection_node: public dependent_node
{
  property res;
  long hyps;
 public:
  intersection_node(node *n1, node *n2);
  ~intersection_node() { delete_hyps(hyps, graph->get_hypotheses()); }
  virtual property const &get_result() const { return res; }
  virtual long get_hyps() const { return hyps; }
  virtual property maximal() const { return res.null() ? res : node::maximal(); }
  virtual property maximal_for(node const *) const;
  virtual void enlarge(property const &p) { res = boundify(p, res); }
};

/**
 * Creates a node proving a property that is an intersection between the results of two nodes @a n1 and @a n2.
 *
 * Calls graph_t::set_contradiction if the new node proves an empty result.
 *
 * @note Predecessors are ordered so that the first one is "less than" the second one.
 */
intersection_node::intersection_node(node *n1, node *n2)
  : dependent_node(INTERSECTION)
{
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
  if (is_empty(res.bnd()))
  {
    if (res1.real.pred() == PRED_REL)
    {
      // "always 0" is not a contradiction, so bail out and hope nobody encounters it
      std::cerr << "Sorry, not implemented: Contradiction on relative errors.\n";
      exit(1);
      return;
    }
    res = property();
    top_graph->set_contradiction(this);
  }
}

/**
 * Extends the interval of the left predecessor towards minus infinity and the
 * interval of the right predecessor towards plus infinity.
 */
property intersection_node::maximal_for(node const *n) const
{
  node_vect const &v = get_subproofs();
  number l = number::neg_inf, u = number::pos_inf;
  if (res.null())
  {
    // TODO: improve bounds
    if (n == v[0]) u = upper(v[0]->get_result().bnd());
    else l = lower(v[1]->get_result().bnd());
  }
  else
  {
    if (n == v[0])
      u = upper(res.bnd());
    else
      l = lower(res.bnd());
  }
  return property(n->get_result().real, interval(l, u));
}

/**
 * Creates a new graph with stronger hypotheses @a h than the parent graph @a f.
 * \li Marks all the parent nodes in #known_reals as known in this new graph too.
 * \li Tries to add ::HYPOTHESIS nodes corresponding to bounded interval hypotheses of @a h.
 * \li Adds other hypotheses of @a h in #partial_reals.
 */
graph_t::graph_t(graph_t *f, property_vect const &h)
  : father(f), hyp(h), contradiction(NULL)
{
  graph_loader loader(this);
  if (f)
  {
    assert(hyp.implies(f->hyp));
    assert(!f->contradiction);
    known_reals = f->known_reals;
    for (node_map::iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
      ++i->second->nb_good;
  }
  for (property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
  {
    interval const &bnd = i->bnd();
    if (!is_bounded(bnd))
    {
      if (known_reals.count(i->real) == 0)
        partial_reals.insert(std::make_pair(i->real, new hypothesis_node(*i)));
    }
    else try_real(new hypothesis_node(*i));
  }
}

/**
 * Empties #known_reals and #partial_reals.
 */
void graph_t::purge()
{
  for(node_map::const_iterator i = known_reals.begin(), end = known_reals.end(); i != end; ++i)
    i->second->remove_known();
  for(node_map::const_iterator i = partial_reals.begin(), end = partial_reals.end(); i != end; ++i)
    delete i->second;
  known_reals.clear();
  partial_reals.clear();
}

/**
 * Sets @a n in #contradiction and increases its node::nb_good reference count. Purges the graph.
 */
void graph_t::set_contradiction(node *n)
{
  assert(n && !contradiction);
  contradiction = n;
  ++n->nb_good;
  purge();
}

int stat_successful_th = 0, stat_discarded_pred = 0, stat_intersected_pred = 0;

/**
 * Remembers @a n if it is worth it. Deletes it otherwise.
 *
 * A node is worth it, if
 * \li the real of its result is not yet known, or
 * \li its result is not a superset of an already known result, or
 * \li its result is equal to an already known result but it has a smaller weight.
 *
 * If the result is new, the function tests the node against #partial_reals and creates an ::intersection_node if any real match.
 *
 * If the result is not a strict subset, an ::intersection_node with the alreay known result is created.
 *
 * @return true is the node is worth it.
 */
bool graph_t::try_real(node *n)
{
  assert(top_graph == this && !contradiction);
  assert(n && n->graph && n->graph->dominates(this));
  property const &res2 = n->get_result();
  ++stat_successful_th;
  std::pair< node_map::iterator, bool > ib = known_reals.insert(std::make_pair(res2.real, n));
  node *&dst = ib.first->second;
  if (!ib.second)
  {
    // there was already a known range
    node *old = dst;
    property const &res1 = old->get_result();
    if (res1.strict_implies(res2))
    {
      ++stat_discarded_pred;
      delete n;
      return false;
    }
    if (res1.implies(res2))
    {
      if (n->get_weight() >= old->get_weight() &&
          n->nb_missing >= old->nb_missing)
      {
        ++stat_discarded_pred;
        delete n;
        return false;
      }
    }
    else if (!res2.strict_implies(res1))
    {
      ++stat_intersected_pred;
      n = new intersection_node(old, n);
      if (n == contradiction) return true;
    }
    dst = n;
    old->remove_known();
  }
  else
  {
    node_map::iterator i = partial_reals.find(res2.real);
    if (i != partial_reals.end())
    {
      // there is a known inequality
      node *m = i->second;
      partial_reals.erase(i);
      property const &res1 = m->get_result();
      if (!res2.implies(res1))
      {
        node *old = n;
        ++n->nb_good; // n has just become a known real, this data is needed in case a contradiction is found
        n = new intersection_node(n, m);
        if (n == contradiction) return true;
        dst = n;
        --old->nb_good;
      }
      else delete m;
    }
  }
  ++n->nb_good;
  return true;
}

/**
 * Returns the best node proving a result on real @a real.
 */
node *graph_t::find_already_known(predicated_real const &real) const
{
  node_map::const_iterator i = known_reals.find(real);
  return i != known_reals.end() ? i->second : NULL;
}

/**
 * Deletes the #contradiction node if any, otherwise purges the graph.
 * No nodes should remain in the graph after these deletions.
 */
graph_t::~graph_t()
{
  if (contradiction)
  {
    --contradiction->nb_good;
    delete contradiction;
  }
  else
    purge();
  assert(nodes.empty());
}

/**
 * Replaces the known reals by the nodes from @a v which are usually weaker and a subset of #known_reals.
 * Purges #partial_reals too.
 * @note This function is meant to be called once the graph is complete, in order to retain only the nodes useful to prove the user proposition.
 */
void graph_t::replace_known(node_vect const &v)
{
  node_map old;
  old.swap(known_reals);
  for (node_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i)
  {
    node *n = *i;
    ++n->nb_good;
    known_reals.insert(std::make_pair(n->get_result().real, n));
  }
  for (node_map::const_iterator i = old.begin(), end = old.end(); i != end; ++i)
    i->second->remove_known();
  for (node_map::const_iterator i = partial_reals.begin(), end = partial_reals.end(); i != end; ++i)
    delete i->second;
  partial_reals.clear();
}

/**
 * Displays the nodes with assumed results in unconstrained mode.
 * Assumed results are associated to a special theorem with the name "$FALSE".
 */
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

/**
 * Scans the nodes of the graph from goals to hypotheses and tries to weaken results.
 */
void enlarger(node_vect const &nodes)
{
  ++visit_counter;
  node_list pending;
  for (node_vect::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i)
    if ((*i)->can_visit()) pending.push_back(*i);
  for (node_list::iterator i = pending.begin(); i != pending.end(); ++i)
  {
    node_vect const &v = (*i)->get_subproofs();
    for (node_vect::const_iterator j = v.begin(), end = v.end(); j != end; ++j)
      if ((*j)->can_visit()) pending.push_back(*j);
  }
  while (!pending.empty())
  {
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
    for (node_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i)
      if ((*i)->can_visit()) pending.push_back(*i);
  }
}
