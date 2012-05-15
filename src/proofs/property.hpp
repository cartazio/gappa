/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PROOFS_PROPERTY_HPP
#define PROOFS_PROPERTY_HPP

#include <cassert>
#include <vector>
#include "numbers/interval.hpp"
#include "parser/ast_real.hpp"

enum predicate_type
{
  PRED_BND = 0, PRED_ABS, PRED_REL,
  PRED_FIX = 4, PRED_FLT,
  PRED_EQL = 8, PRED_NZR
};

class predicated_real {
  long d1, d2;
 public:
  predicated_real(): d1(0), d2(0) {}
  predicated_real(ast_real const *r, predicate_type p)
    : d1(reinterpret_cast< long >(r) | (p & 3)), d2(p >> 2) {}
  predicated_real(ast_real const *r1, ast_real const *r2, predicate_type p)
    : d1(reinterpret_cast< long >(r1) | (p & 3)), d2(reinterpret_cast< long >(r2) | (p >> 2)) {}
  predicate_type pred() const { return (predicate_type)((d1 & 3) | ((d2 & 3) << 2)); }
  bool pred_bnd() const { return (d2 & 3) == 0; }
  bool pred_cst() const { return (d2 & 3) == 1; }
  ast_real const *real()  const { return reinterpret_cast< ast_real const * >(d1 & ~3); }
  ast_real const *real2() const { return reinterpret_cast< ast_real const * >(d2 & ~3); }
  bool operator==(predicated_real const &r) const { return d1 == r.d1 && d2 == r.d2; }
  bool operator!=(predicated_real const &r) const { return d1 != r.d1 || d2 != r.d2; }
  bool operator< (predicated_real const &r) const { return d1 < r.d1 || (d1 == r.d1 && d2 < r.d2); }
  bool null() const { return d1 == 0; }
};

typedef std::vector< predicated_real > preal_vect;

class property {
  union store_t {
    char _bnd[sizeof(interval)];
    long _int;
  };
  store_t store;
  interval       &_bnd()       { return *reinterpret_cast< interval       * >(&store); }
  interval const &_bnd() const { return *reinterpret_cast< interval const * >(&store); }
 public:
  predicated_real real;
  interval &bnd()
  { assert(real.pred_bnd()); return _bnd(); }
  interval const &bnd() const
  { assert(real.pred_bnd()); return _bnd(); }
  long &cst()
  { assert(real.pred_cst()); return store._int; }
  long const &cst() const
  { assert(real.pred_cst()); return store._int; }
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

struct split_point;

typedef std::multiset<split_point> split_point_mset;
typedef std::map<predicated_real, split_point_mset> splitting;

struct property_tree
{
  //* Second member is true if the property is in the goal.
  typedef std::pair< property, bool > leave;
  struct data {
    std::vector< leave > leaves;
    std::vector< property_tree > subtrees;
    unsigned ref;
    bool conjunction;
    data(bool b): ref(0), conjunction(b) {}
  };
 private:
  data *ptr;
  void incr() { if (ptr) ++ptr->ref; }
  void decr() { if (ptr && --ptr->ref == 0) delete ptr; }
  void flatten();
  bool get_nodes_aux(std::vector< std::pair< node *, interval > > &) const;
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
  data const *operator->() const { return ptr; }
  data *operator->() { unique(); return ptr; }
  bool empty() const { return !ptr; }

  /**
   * Fills leaves that have an undefined interval with a corresponding
   * interval from @a p. Removes leaves for which no interval can be found.
   */
  void fill_undefined(property_tree const &p);

  /**
   * Simplifies the tree according to property @a p.
   * @param force If true, the function removes undefined yet matching leaves.
   * @return zero if the tree is not empty yet, a positive value if it is
   *         true, a negative value if it is false.
   */
  int simplify(property const &p, bool positive = true, bool force = false);

  /**
   * Checks if the tree is satisfied by graph @a g.
   * @param p Pointer to an optional storage for an unsatisfied property.
   * @return false if some properties are not satisfied.
   */
  bool verify(graph_t *g, property *p) const;

  /**
   * Gets the nodes of graph @a g satisfying the property.
   * Removes the satisfied leaves and subtrees.
   */
  void get_nodes(graph_t *g, std::vector< node * > &);

  void get_splitting(splitting &) const;
};

struct context {
  property_vect hyp;
  property_tree goals;
};

#endif // PROOFS_PROPERTY_HPP
