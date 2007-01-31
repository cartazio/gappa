#ifndef PROOFS_SCHEMES_HPP
#define PROOFS_SCHEMES_HPP

#include "parser/ast_real.hpp"
#include "proofs/proof_graph.hpp"

typedef std::vector< predicated_real > preal_vect;

struct proof_scheme {
  virtual node *generate_proof() const = 0;
  virtual preal_vect needed_reals() const = 0;
  virtual ~proof_scheme() {}
  proof_scheme(ast_real const *r): real(r, PRED_BND) {}
  proof_scheme(predicated_real const &r): real(r) {}
  predicated_real real;
  mutable bool scanned;
};

struct scheme_factory {
  predicated_real target;
  scheme_factory(predicated_real const &r);
  virtual proof_scheme *operator()(predicated_real const &, ast_real_vect const &) const = 0;
  virtual ~scheme_factory() {}
};

struct factory_creator {
  typedef proof_scheme *(*factorx_fun)(predicated_real const &, ast_real_vect const &);
  typedef proof_scheme *(*factory_fun)(ast_real const *);
  typedef proof_scheme *(*factorz_fun)(predicated_real const &);
  factory_creator(factorx_fun f);
  factory_creator(factory_fun f);
  factory_creator(factorz_fun f);
};

#define REGISTER_SCHEME_BEGIN(name) \
  struct name##_scheme: proof_scheme { \
    virtual node *generate_proof() const; \
    virtual preal_vect needed_reals() const; \
    static proof_scheme *factory(ast_real const *)

#define REGISTER_SCHEME_END(name) \
  }; \
  static factory_creator name##_scheme_register(&name##_scheme::factory)

#define REGISTER_SCHEMEX_BEGIN(name) \
  struct name##_scheme: proof_scheme { \
    virtual node *generate_proof() const; \
    virtual preal_vect needed_reals() const; \
    static proof_scheme *factory(predicated_real const &)

#define REGISTER_SCHEMEX_END(name) \
  }; \
  static factory_creator name##_scheme_register(&name##_scheme::factory)

#define REGISTER_SCHEMEY_BEGIN(name) \
  struct name##_scheme: proof_scheme { \
    virtual node *generate_proof() const; \
    virtual preal_vect needed_reals() const; \
    static proof_scheme *factory(predicated_real const &, ast_real_vect const &)

#define REGISTER_SCHEMEY_END(name) \
  }; \
  static factory_creator name##_scheme_register(&name##_scheme::factory)

inline node *find_proof(predicated_real const &real) { return top_graph->find_already_known(real); }
node *find_proof(property const &);
bool fill_hypotheses(property *, preal_vect const &);

ast_real_vect generate_proof_paths();

#endif // PROOFS_SCHEMES_HPP
