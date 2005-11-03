#ifndef PROOFS_PROPERTY_HPP
#define PROOFS_PROPERTY_HPP

#include <cassert>
#include <vector>
#include "numbers/interval.hpp"
#include "parser/ast_real.hpp"

enum predicate_type { PRED_BND, PRED_FIX, PRED_FLT };

class predicated_real {
  long d;
 public:
  predicated_real(): d(0) {}
  predicated_real(ast_real const *r, predicate_type p): d(reinterpret_cast< long >(r) | p) {}
  predicate_type pred() const { return (predicate_type)(d & 3); }
  ast_real const *real() const { return reinterpret_cast< ast_real const * >(d & ~3); }
  bool operator==(predicated_real const &r) const { return d == r.d; }
  bool operator!=(predicated_real const &r) const { return d != r.d; }
  bool operator< (predicated_real const &r) const { return d <  r.d; }
  bool null() const { return d == 0; }
};

class property {
  long d;
 public:
  predicated_real real;
  interval &bnd()
  { assert(real.pred() == PRED_BND); return *reinterpret_cast< interval * >(&d); }
  interval const &bnd() const
  { assert(real.pred() == PRED_BND); return *reinterpret_cast< interval const * >(&d); }
  long &cst()
  { assert(real.pred() != PRED_BND); return d; }
  long const &cst() const
  { assert(real.pred() != PRED_BND); return d; }
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

class property_vect {
  typedef std::vector< property > vect;
  vect vec;
 public:
  bool implies(property_vect const &) const;
  int find_compatible_property(property const &) const;
  void push_back(property const &p) { vec.push_back(p); }
  void push_front(property const &);
  typedef vect::const_iterator const_iterator;
  const_iterator begin() const { return vec.begin(); }
  const_iterator end  () const { return vec.end  (); }
  property const &operator[](unsigned i) const { return vec[i]; }
  void replace_front(property const &);
  unsigned size() const { return vec.size(); }
};

struct context {
  property_vect hyp;
  property_vect goals;
};

typedef std::vector< context > context_vect;
extern context_vect contexts;
extern context const *current_context;

#endif // PROOFS_PROPERTY_HPP
