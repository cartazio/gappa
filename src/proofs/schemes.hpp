#ifndef PROOFS_SCHEMES_HPP
#define PROOFS_SCHEMES_HPP

#include "parser/ast_real.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/proof_graph.hpp"

struct proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const = 0;
  virtual ast_real_vect needed_reals(ast_real const *) const = 0;
  virtual ~proof_scheme() {}
  proof_scheme(): next(NULL) {}
  proof_scheme const *next;
};

struct scheme_factory {
  virtual proof_scheme *operator()(ast_real const *) const = 0;
  virtual ~scheme_factory() {}
};

struct scheme_register {
  typedef proof_scheme *(*scheme_factory_fun)(ast_real const *);
  static std::vector< scheme_factory const * > factories;
  scheme_register(scheme_factory_fun f);
  scheme_register(scheme_factory const *);
  typedef std::vector< scheme_factory const * >::const_iterator iterator;
  static iterator begin() { return factories.begin(); }
  static iterator end  () { return factories.end  (); }
};

node *handle_proof(property_vect const &, property &);
bool generate_scheme_tree(property_vect const &hyp, ast_real const *);

#endif // PROOFS_SCHEMES_HPP
