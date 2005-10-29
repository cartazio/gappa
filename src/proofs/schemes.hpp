#ifndef PROOFS_SCHEMES_HPP
#define PROOFS_SCHEMES_HPP

#include "parser/ast_real.hpp"
#include "proofs/proof_graph.hpp"

typedef std::vector< predicated_real > preal_vect;

struct proof_scheme {
  virtual node *generate_proof() const = 0;
  virtual node *generate_proof(interval const &) const { return generate_proof(); }
  virtual preal_vect needed_reals() const = 0;
  virtual bool dummy() const { return false; }
  virtual ~proof_scheme() {}
  proof_scheme(ast_real const *r): real(r, PRED_BND) {}
  proof_scheme(predicated_real const &r): real(r) {}
  predicated_real real;
};

struct scheme_factory {
  virtual proof_scheme *operator()(predicated_real const &) const = 0;
  virtual ~scheme_factory() {}
};

struct scheme_register {
  typedef proof_scheme *(*scheme_factory_fun)(ast_real const *);
  typedef proof_scheme *(*scheme_factorz_fun)(predicated_real const &);
  scheme_register(scheme_factory_fun f);
  scheme_register(scheme_factorz_fun f);
  scheme_register(scheme_factory const *);
};

#define REGISTER_SCHEME_BEGIN(name) \
  struct name##_scheme: proof_scheme { \
    virtual node *generate_proof() const; \
    virtual preal_vect needed_reals() const; \
    static proof_scheme *factory(ast_real const *)

#define REGISTER_SCHEME_END(name) \
  }; \
  static scheme_register name##_scheme_register(&name##_scheme::factory)

#define REGISTER_SCHEMEX_BEGIN(name) \
  struct name##_scheme: proof_scheme { \
    virtual node *generate_proof() const; \
    virtual preal_vect needed_reals() const; \
    static proof_scheme *factory(predicated_real const &)

#define REGISTER_SCHEMEX_END(name) \
  }; \
  static scheme_register name##_scheme_register(&name##_scheme::factory)

inline node *find_proof(predicated_real const &real) { return top_graph->find_already_known(real); }
node *find_proof(property const &);
bool fill_hypotheses(property *, preal_vect const &);

ast_real_vect generate_proof_paths();

#endif // PROOFS_SCHEMES_HPP
