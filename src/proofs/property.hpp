#ifndef PROOFS_PROPERTY_HPP
#define PROOFS_PROPERTY_HPP

#include <cassert>
#include <set>
#include <vector>
#include "numbers/interval.hpp"
#include "parser/ast_real.hpp"

enum predicate_type { PRED_BND, PRED_ABS, PRED_FIX, PRED_FLT };

class predicated_real {
  long d;
 public:
  predicated_real(): d(0) {}
  predicated_real(ast_real const *r, predicate_type p): d(reinterpret_cast< long >(r) | p) {}
  predicate_type pred() const { return (predicate_type)(d & 3); }
  bool pred_bnd() const { return (d & 2) == 0; }
  bool pred_cst() const { return (d & 2) != 0; }
  ast_real const *real() const { return reinterpret_cast< ast_real const * >(d & ~3); }
  bool operator==(predicated_real const &r) const { return d == r.d; }
  bool operator!=(predicated_real const &r) const { return d != r.d; }
  bool operator< (predicated_real const &r) const { return d <  r.d; }
  bool null() const { return d == 0; }
};

class property {
  union {
    char store_bnd[sizeof(interval)];
    long store_int;
  };
  interval       &_bnd()       { return *reinterpret_cast< interval       * >(&store_bnd); }
  interval const &_bnd() const { return *reinterpret_cast< interval const * >(&store_bnd); }
 public:
  predicated_real real;
  interval &bnd()
  { assert(real.pred_bnd()); return _bnd(); }
  interval const &bnd() const
  { assert(real.pred_bnd()); return _bnd(); }
  long &cst()
  { assert(real.pred_cst()); return store_int; }
  long const &cst() const
  { assert(real.pred_cst()); return store_int; }
  property();
  property(ast_real const *);
  property(ast_real const *, interval const &);
  property(predicated_real const &);
  property(predicated_real const &, interval const &);
  property(predicated_real const &, long);
  property(property const &);
  property &operator=(property const &);
  ~property();
  bool implies(property const &) const;
  bool strict_implies(property const &) const;
  void intersect(property const &);
  void hull(property const &);
  bool null() const { return real.null(); }
};

struct property_vect: std::vector< property > {
  bool implies(property_vect const &) const;
  int find_compatible_property(property const &) const;
};

struct node;
struct graph_t;

struct property_tree {
  struct data {
    std::vector< property > leafs;
    std::vector< property_tree > subtrees;
    unsigned ref;
    bool conjonction;
    data(bool b): ref(0), conjonction(b) {}
  };
 private:
  data *ptr;
  void incr() { if (ptr) ++ptr->ref; }
  void decr() { if (ptr && --ptr->ref == 0) delete ptr; }
  void flatten();
 public:
  property_tree(): ptr(NULL) {}
  property_tree(data *p): ptr(p) { incr(); }
  property_tree(property_tree const &t): ptr(t.ptr) { incr(); }
  property_tree &operator=(data *p)
  { if (ptr != p) { decr(); ptr = p; incr(); } return *this; }
  property_tree &operator=(property_tree const &t)
  { if (ptr != t.ptr) { decr(); ptr = t.ptr; incr(); } return *this; }
  ~property_tree() { decr(); }
  void unique();
  void restrict(ast_real_vect const &);
  data const *operator->() const { return ptr; }
  data *operator->() { unique(); return ptr; }
  bool empty() const { return !ptr; }
  bool remove(property const &);		// false if the tree is not yet fully satisfied
  bool verify(graph_t *, property *) const;	// false if some branches are not satisfied
  bool get_nodes(graph_t *, std::set< node * > &) const;
};

struct context {
  property_vect hyp;
  property_tree goals;
  std::vector< int > deps;
};

typedef std::vector< context > context_vect;
extern context_vect contexts;

#endif // PROOFS_PROPERTY_HPP
