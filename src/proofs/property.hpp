#ifndef PROOFS_PROPERTY_HPP
#define PROOFS_PROPERTY_HPP

#include "numbers/interval.hpp"
#include "parser/ast_real.hpp"
#include <vector>

struct property {
  ast_real const *real;
  interval bnd;
  property(): real(NULL) {}
  property(ast_real const *r): real(r) {}
  property(ast_real const *r, interval const &b): real(r), bnd(b) {}
  bool implies(property const &) const;
  bool operator<(property const &) const;
};

class property_vect {
  typedef std::vector< property > vect;
  vect vec;
  int well_known;
  vect const &get() const;
 public:
  property_vect(): well_known(-1) {}
  property_vect(property_vect const &p): vec(p.vec), well_known(p.well_known) {}
  bool implies(property_vect const &) const;
  int find_compatible_property(property const &) const;
  bool operator==(property_vect const &) const;
  void push_back(property const &);
  void push_front(property const &);
  typedef vect::const_iterator const_iterator;
  const_iterator begin() const;
  const_iterator end() const;
  property const &operator[](unsigned) const;
  void replace_front(property const &);
  unsigned size() const;
  void publish();
};

#endif // PROOFS_PROPERTY_HPP
