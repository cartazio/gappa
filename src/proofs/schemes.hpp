#ifndef PROOFS_SCHEMES_HPP
#define PROOFS_SCHEMES_HPP

#include "parser/ast_real.hpp"
#include "proofs/proof_graph.hpp"

struct proof_scheme {
  virtual node *generate_proof() const = 0;
  virtual node *generate_proof(interval const &) const;
  virtual ast_real_vect needed_reals() const = 0;
  virtual ~proof_scheme() {}
  proof_scheme(ast_real const *r): real(r) {}
  ast_real const *real;
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

node *find_proof(ast_real const *);
node *find_proof(property const &);
bool generate_scheme_tree(ast_real const *, proof_scheme_list &, ast_real_vect &);

#endif // PROOFS_SCHEMES_HPP
