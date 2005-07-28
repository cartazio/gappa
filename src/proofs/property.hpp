#ifndef PROOFS_PROPERTY_HPP
#define PROOFS_PROPERTY_HPP

#include <vector>
#include "numbers/interval.hpp"
#include "parser/ast_real.hpp"

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
 public:
  bool implies(property_vect const &) const;
  int find_compatible_property(property const &) const;
  bool operator==(property_vect const &) const;
  void push_back(property const &p) { vec.push_back(p); }
  void push_front(property const &);
  typedef vect::const_iterator const_iterator;
  const_iterator begin() const { return vec.begin(); }
  const_iterator end  () const { return vec.end  (); }
  property const &operator[](unsigned i) const { return vec[i]; }
  void replace_front(property const &);
  unsigned size() const { return vec.size(); }
};

#endif // PROOFS_PROPERTY_HPP
