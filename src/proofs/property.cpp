#include <algorithm>
#include <climits>
#include <new>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/property.hpp"
#include "proofs/schemes.hpp"

typedef int long_is_not_long_enough_1[2 * (sizeof(long) >= sizeof(void *)) - 1];
typedef int long_is_not_long_enough_2[2 * (sizeof(long) >= sizeof(interval)) - 1];

property::property(): real() { store._int = 0; }

property::property(ast_real const *r): real(r, PRED_BND) {
  new(&store) interval;
}

property::property(ast_real const *r, interval const &i): real(r, PRED_BND) {
  new(&store) interval(i);
}

property::property(predicated_real const &r): real(r) {
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: new(&store) interval; break;
  case PRED_FIX: store._int = INT_MIN; break;
  case PRED_FLT: store._int = INT_MAX; break;
  case PRED_NZR: break;
  }
}

property::property(predicated_real const &r, interval const &i): real(r) {
  assert(r.pred_bnd());
  new(&store) interval(i);
}

property::property(predicated_real const &r, long i): real(r)
{
  assert(r.pred_cst());
  store._int = i;
}

property::property(property const &p): real(p.real) {
  if (p.real.pred_bnd()) new(&store) interval(p._bnd());
  else store._int = p.store._int;
}

property::~property() {
  if (real.pred_bnd()) _bnd().~interval();
}

property &property::operator=(property const &p) {
  if (p.real.pred_bnd()) {
    interval const &pb = p._bnd();
    if (real.pred_bnd()) _bnd() = pb;
    else new(&store) interval(pb);
  } else {
    if (real.pred_bnd()) _bnd().~interval();
    store._int = p.store._int;
  }
  real = p.real;
  return *this;
}

bool property::implies(property const &p) const {
  if (real != p.real) return false;
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: return _bnd() <= p._bnd();
  case PRED_FIX: return store._int >= p.store._int;
  case PRED_FLT: return store._int <= p.store._int;
  case PRED_NZR: return true;
  }
  assert(false);
  return false;
}

bool property::strict_implies(property const &p) const {
  if (real != p.real) return false;
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: return _bnd() < p._bnd();
  case PRED_FIX: return store._int > p.store._int;
  case PRED_FLT: return store._int < p.store._int;
  case PRED_NZR: return false;
  }
  assert(false);
  return false;
}

void property::intersect(property const &p) {
  assert(real == p.real);
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: _bnd() = ::intersect(_bnd(), p._bnd()); break;
  case PRED_FIX: store._int = std::max(store._int, p.store._int); break;
  case PRED_FLT: store._int = std::min(store._int, p.store._int); break;
  case PRED_NZR: break;
  }
}


void property::hull(property const &p) {
  assert(real == p.real);
  switch (real.pred()) {
  case PRED_ABS:
  case PRED_REL:
  case PRED_BND: _bnd() = ::hull(_bnd(), p._bnd()); break;
  case PRED_FIX: store._int = std::min(store._int, p.store._int); break;
  case PRED_FLT: store._int = std::max(store._int, p.store._int); break;
  case PRED_NZR: break;
  }
}

bool property_vect::implies(property_vect const &s) const {
  for(const_iterator i = s.begin(), i_end = s.end(); i != i_end; ++i) {
    bool implies_i = false;
    for(const_iterator j = begin(), j_end = end(); j != j_end; ++j)
      if (j->implies(*i)) { implies_i = true; break; }
    if (!implies_i) return false;
  }
  return true;
}

int property_vect::find_compatible_property(property const &p) const {
  for(const_iterator i_begin = begin(), i = i_begin, i_end = end(); i != i_end; ++i)
    if (i->implies(p)) return i - i_begin;
  return -1;
}

void property_tree::unique() {
  if (ptr && ptr->ref > 1) {
    data *p = new data(*ptr);
    p->ref = 1;
    --ptr->ref;
    ptr = p;
  }
}

/**
 * Helper class for filtering out leaves that are satisfied by a given
 * property.
 */
struct remove_pred1
{
  property const &prop;
  bool force, unrelated;
  remove_pred1(property const &p, bool f)
    : prop(p), force(f), unrelated(false) {}
  bool operator()(property_tree::leave &p)
  {
    if (p.first.real == prop.real) {
      if (!is_defined(p.first.bnd())) return force || !p.second;
      if (p.second) {
        if (prop.implies(p.first)) return true;
      } else {
        property q = p.first;
        q.intersect(prop);
        if (is_empty(q.bnd())) return true;
      }
    }
    unrelated = true;
    return false;
  }
};

/**
 * Helper class for filtering out (and recursively pruning) subtrees that
 * are satisfied by a given property.
 */
struct remove_pred2 {
  property const &prop;
  bool force, unrelated;
  remove_pred2(property const &p, bool f)
    : prop(p), force(f), unrelated(false) {}
  bool operator()(property_tree &t)
  {
    bool b = t.remove(prop, force);
    if (t.empty()) return true;
    if (!b) unrelated = true;
    return false;
  }
};

void property_tree::flatten()
{
  bool possible = false;
  for (std::vector<property_tree>::const_iterator i = ptr->subtrees.begin(),
       i_end = ptr->subtrees.end(); i != i_end; ++i)
  {
    if (i->ptr->conjunction != ptr->conjunction &&
        i->ptr->leaves.size() + i->ptr->subtrees.size() > 1) continue;
    possible = true;
    break;
  }
  if (!possible)
  {
    if (ptr->subtrees.size() != 1) return;
    property_tree &t = ptr->subtrees[0];
    if (!ptr->leaves.empty() && t.ptr->conjunction != ptr->conjunction) return;
    // The root is a singleton or its only subtree has a compatible
    // modality; replace the root with it.
    t.unique();
    data *p = t.ptr;
    p->leaves.insert(p->leaves.end(), ptr->leaves.begin(), ptr->leaves.end());
    ++p->ref; // have to "incr" before decr; decr may erase t otherwise
    decr();
    ptr = p;
    return;
  }
  // Some subtrees are singleton or have a modality compatible with the
  // root; merge them into the root.
  unique();
  std::vector<property_tree> old_trees;
  old_trees.swap(ptr->subtrees);
  for (std::vector<property_tree>::const_iterator i = old_trees.begin(),
       i_end = old_trees.end(); i != i_end; ++i)
  {
    if (i->ptr->conjunction != ptr->conjunction &&
        i->ptr->leaves.size() + i->ptr->subtrees.size() > 1) {
      ptr->subtrees.push_back(*i);
      continue;
    }
    ptr->subtrees.insert(ptr->subtrees.end(), i->ptr->subtrees.begin(), i->ptr->subtrees.end());
    ptr->leaves.insert(ptr->leaves.end(), i->ptr->leaves.begin(), i->ptr->leaves.end());
  }
}

bool property_tree::remove(property const &p, bool force)
{
  if (!ptr) return true;
  unique();
  assert(p.real.pred() == PRED_BND || p.real.pred() == PRED_REL);
  {
  // Filter out satisfied leaves.
  remove_pred1 pred1(p, force);
  std::vector< leave >::iterator end1 = ptr->leaves.end(),
    i1 = std::remove_if(ptr->leaves.begin(), end1, pred1);
  if (i1 != end1 && !ptr->conjunction) goto kill_tree;
  // Filter out satisfied subtrees.
  remove_pred2 pred2(p, force);
  std::vector< property_tree >::iterator end2 = ptr->subtrees.end(),
    i2 = std::remove_if(ptr->subtrees.begin(), end2, pred2);
  if (i2 != end2 && !ptr->conjunction) goto kill_tree;
  ptr->leaves.erase(i1, end1);
  ptr->subtrees.erase(i2, end2);
  if (ptr->leaves.empty() && ptr->subtrees.empty()) goto kill_tree;
  flatten();
  return !pred1.unrelated && !pred2.unrelated;
  }
 kill_tree:
  decr();
  ptr = NULL;
  return true;
}

bool property_tree::verify(graph_t *g, property *p) const
{
  if (!ptr) return false;
  graph_loader loader(g);
  bool b = ptr->conjunction;
  for (std::vector< leave >::const_iterator i = ptr->leaves.begin(),
       i_end = ptr->leaves.end(); i != i_end; ++i)
  {
    if (b == !!find_proof(i->first, i->second)) continue;
    // Either this tree node is a conjunction and property *i is not satisfied,
    // or it is a disjunction and property *i is satisfied.
    if (b && p) *p = i->first;
    return !b;
  }
  for (std::vector< property_tree >::const_iterator i = ptr->subtrees.begin(),
       end = ptr->subtrees.end(); i != end; ++i)
  {
    if (b == i->verify(g, b ? p : NULL)) continue;
    // Same here, but for the *i subtree.
    return !b;
  }
  // Either the tree node is a conjunction and all its properties are satisfied,
  // or it is a disjunction and none are satisfied.
  return b;
}

struct goal_node: node {
  property res;
  node *pred;
  goal_node(property const &p, node *n): node(GOAL, top_graph), res(p), pred(n)
  { n->succ.insert(this); }
  virtual property const &get_result() const { return res; }
  virtual node_vect const &get_subproofs() const;
  virtual void enlarge(property const &) { assert(false); }
  virtual property maximal() const { return res; }
  virtual property maximal_for(node const *) const { return res; }
  virtual ~goal_node() { pred->remove_succ(this); }
};

node_vect const &goal_node::get_subproofs() const {
  static node_vect v(1);
  v[0] = pred;
  return v;
}

typedef std::vector< std::pair< node *, interval > > goal_vect;

bool property_tree::get_nodes_aux(goal_vect &goals) const
{
  bool all = true;
  for (std::vector< leave >::const_iterator i = ptr->leaves.begin(),
       i_end = ptr->leaves.end(); i != i_end; ++i)
  {
    if (node *n = find_proof(i->first, i->second)) {
      goals.push_back(std::make_pair(n, i->first.bnd()));
      if (!ptr->conjunction) return true;
    } else all = false;
  }
  if (ptr->conjunction) {
    for(std::vector< property_tree >::const_iterator i = ptr->subtrees.begin(),
        end = ptr->subtrees.end(); i != end; ++i)
      if (!i->get_nodes_aux(goals)) all = false;
    return all;
  } else {
    unsigned sz = goals.size();
    for(std::vector< property_tree >::const_iterator i = ptr->subtrees.begin(),
        end = ptr->subtrees.end(); i != end; ++i) {
      if (i->get_nodes_aux(goals)) return true;
      goals.erase(goals.begin() + sz, goals.end());
    }
    return false;
  }
}

void property_tree::get_nodes(graph_t *g, node_vect &goals)
{
  assert(ptr);
  graph_loader loader(g);
  goal_vect gs;
  get_nodes_aux(gs);
  typedef std::map< node *, interval > node_map;
  node_map m;
  for(goal_vect::const_iterator i = gs.begin(), end = gs.end(); i != end; ++i) {
    node_map::iterator j = m.find(i->first);
    if (j == m.end())
      m.insert(*i);
    else if (is_defined(i->second)) {
      if (!is_defined(j->second)) j->second = i->second;
      else j->second = intersect(i->second, j->second);
    }
  }
  goals.clear();
  for(node_map::const_iterator i = m.begin(), end = m.end(); i != end; ++i) {
    property p(i->first->get_result());
    if (is_defined(i->second)) p.bnd() = i->second;
    goals.push_back(new goal_node(p, i->first));
    remove(p, true);
  }
  g->replace_known(goals);
}

struct remove_pred3
{
  ast_real_vect const &dst;
  remove_pred3(ast_real_vect const &v): dst(v) {}
  bool operator()(property_tree::leave const &p)
  {
    for (ast_real_vect::const_iterator i = dst.begin(),
         i_end = dst.end(); i != i_end; ++i)
    {
      if (p.second && p.first.real.pred() == PRED_BND &&
          p.first.real.real() == *i && is_defined(p.first.bnd()))
        return false;
    }
    return true;
  }
};

struct remove_pred4 {
  ast_real_vect const &dst;
  remove_pred4(ast_real_vect const &v): dst(v) {}
  bool operator()(property_tree &t) {
    t.restrict(dst);
    return t.empty();
  }
};

void property_tree::restrict(ast_real_vect const &dst) {
  if (!ptr) return;
  unique();
  remove_pred3 pred1(dst);
  remove_pred4 pred2(dst);
  std::vector< leave >::iterator end1 = ptr->leaves.end(),
    i1 = std::remove_if(ptr->leaves.begin(), end1, pred1);
  std::vector< property_tree >::iterator end2 = ptr->subtrees.end(),
    i2 = std::remove_if(ptr->subtrees.begin(), end2, pred2);
  ptr->leaves.erase(i1, end1);
  ptr->subtrees.erase(i2, end2);
  if (ptr->leaves.empty() && ptr->subtrees.empty()) {
    delete ptr;
    ptr = NULL;
  } else flatten();
}
