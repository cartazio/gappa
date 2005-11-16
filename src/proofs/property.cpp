#include <algorithm>
#include <new>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/property.hpp"
#include "proofs/schemes.hpp"

typedef int long_is_not_long_enough[2 * (sizeof(long) >= sizeof(void *)) - 1];

property::property(): d(0), real() {}

property::property(ast_real const *r): real(r, PRED_BND) {
  new(&d) interval;
}

property::property(ast_real const *r, interval const &i): real(r, PRED_BND) {
  new(&d) interval(i);
}

property::property(predicated_real const &r): real(r) {
  switch (real.pred()) {
  case PRED_BND: new(&d) interval; break;
  case PRED_FIX: d = INT_MIN;
  case PRED_FLT: d = INT_MAX;
  }
}

property::property(predicated_real const &r, interval const &i): real(r) {
  assert(r.pred() == PRED_BND);
  new(&d) interval(i);
}

property::property(predicated_real const &r, long i): d(i), real(r) {
  assert(r.pred() != PRED_BND);
}

property::property(property const &p): real(p.real) {
  if (p.real.pred() == PRED_BND) new(&d) interval(p.bnd());
  else d = p.d;
}

property::~property() {
  if (real.pred() == PRED_BND) bnd().~interval();
}

property &property::operator=(property const &p) {
  if (p.real.pred() == PRED_BND) {
    interval const &pb = p.bnd();
    if (real.pred() == PRED_BND) bnd() = pb;
    else new(&d) interval(pb);
  } else {
    if (real.pred() == PRED_BND) bnd().~interval();
    d = p.d;
  }
  real = p.real;
  return *this;
}

bool property::implies(property const &p) const {
  if (real != p.real) return false;
  switch (real.pred()) {
  case PRED_BND: return bnd() <= p.bnd();
  case PRED_FIX: return d >= p.d;
  case PRED_FLT: return d <= p.d;
  }
  assert(false);
  return false;
}

bool property::strict_implies(property const &p) const {
  if (real != p.real) return false;
  switch (real.pred()) {
  case PRED_BND: return bnd() < p.bnd();
  case PRED_FIX: return d > p.d;
  case PRED_FLT: return d < p.d;
  }
  assert(false);
  return false;
}

void property::intersect(property const &p) {
  assert(real == p.real);
  switch (real.pred()) {
  case PRED_BND: { interval &i = bnd(); i = ::intersect(i, p.bnd()); break; }
  case PRED_FIX: d = std::max(d, p.d); break;
  case PRED_FLT: d = std::min(d, p.d); break;
  }
}


void property::hull(property const &p) {
  assert(real == p.real);
  switch (real.pred()) {
  case PRED_BND: { interval &i = bnd(); i = ::hull(i, p.bnd()); break; }
  case PRED_FIX: d = std::min(d, p.d); break;
  case PRED_FLT: d = std::max(d, p.d); break;
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
    for(std::vector< property_tree >::iterator i = ptr->subtrees.begin(),
        end = ptr->subtrees.end(); i != end; ++i)
      if (i->ptr) ++i->ptr->ref;
  }
}

struct remove_pred1 {
  property const &prop;
  bool unrelated;
  remove_pred1(property const &p): prop(p), unrelated(false) {}
  bool operator()(property const &p) {
    if (p.real != prop.real) unrelated = true;
    else if (prop.bnd() <= p.bnd()) return true;
    return false;
  }
};

struct remove_pred2 {
  property const &prop;
  bool unrelated;
  remove_pred2(property const &p): prop(p), unrelated(false) {}
  bool operator()(property_tree &t) {
    bool b = t.remove(prop);
    if (t.empty()) return true;
    if (!b) unrelated = true;
    return false;
  }
};

bool property_tree::remove(property const &p) {
  if (!ptr) return true;
  unique();
  assert(p.real.pred() == PRED_BND);
  remove_pred1 pred1(p);
  remove_pred2 pred2(p);
  std::vector< property >::iterator end1 = ptr->leafs.end(),
    i1 = std::remove_if(ptr->leafs.begin(), end1, pred1);
  std::vector< property_tree >::iterator end2 = ptr->subtrees.end(),
    i2 = std::remove_if(ptr->subtrees.begin(), end2, pred2);
  if (i1 != end1 && !ptr->conjonction) goto kill_tree;
  if (i2 != end2 && !ptr->conjonction) goto kill_tree;
  ptr->leafs.erase(i1, end1);
  ptr->subtrees.erase(i2, end2);
  if (ptr->leafs.empty() && ptr->subtrees.empty()) goto kill_tree;
  if (ptr->subtrees.size() == 1) {
    property_tree &t = ptr->subtrees[0];
    if (ptr->leafs.empty() || t.ptr->conjonction == ptr->conjonction) {
      t.unique();
      data *p = t.ptr;
      p->leafs.insert(p->leafs.end(), ptr->leafs.begin(), ptr->leafs.end());
      ++p->ref; // have to "incr" before decr; decr may erase t otherwise
      decr();
      ptr = p;
    }
  }
  return !pred1.unrelated && !pred2.unrelated;
 kill_tree:
  decr();
  ptr = NULL;
  return true;
}

bool property_tree::get_reals(node_set &goals) const {
  if (!ptr) return true;
  assert(top_graph);
  bool all = true;
  for(std::vector< property >::const_iterator i = ptr->leafs.begin(),
      end = ptr->leafs.end(); i != end; ++i) {
    node *n = find_proof(*i);
    if (!n) { all = false; continue; }
    goals.insert(n);
    if (!ptr->conjonction) return true;
  }
  if (ptr->conjonction) {
    for(std::vector< property_tree >::const_iterator i = ptr->subtrees.begin(),
        end = ptr->subtrees.end(); i != end; ++i)
      if (!i->get_reals(goals)) all = false;
    return all;
  } else {
    for(std::vector< property_tree >::const_iterator i = ptr->subtrees.begin(),
        end = ptr->subtrees.end(); i != end; ++i) {
      node_set tmp;
      if (!i->get_reals(tmp)) continue;
      goals.insert(tmp.begin(), tmp.end());
      return true;
    }
    return false;
  }
}
