#include "proofs/basic_proof.hpp"
#include "proofs/schemes.hpp"

std::vector< scheme_factory const * > scheme_register::factories;

struct scheme_factory_wrapper: scheme_factory {
  typedef scheme_register::scheme_factory_fun scheme_factory_fun;
  scheme_factory_fun fun;
  scheme_factory_wrapper(scheme_factory_fun f): fun(f) {}
  virtual proof_scheme *operator()(ast_real const *r) const { return (*fun)(r); }
};

scheme_register::scheme_register(scheme_factory_fun f) {
  factories.push_back(new scheme_factory_wrapper(f));
}

scheme_register::scheme_register(scheme_factory const *f) {
  factories.push_back(f);
}

struct no_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const { return NULL; }
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
};

struct yes_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const { return NULL; }
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
};

bool generate_scheme_tree(property_vect const &hyp, ast_real const *r) {
  if (r->scheme) return !dynamic_cast< no_scheme const * >(r->scheme);
  r->scheme = new yes_scheme;
  std::vector< proof_scheme * > schemes;
  for(scheme_register::factory_iterator i = scheme_register::factories.begin(), i_end = scheme_register::factories.end();
      i != i_end; ++i) {
    proof_scheme *s = (**i)(r);
    if (!s) continue;
    ast_real_vect v = s->needed_reals(r);
    bool good = true;
    for(ast_real_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j) {
      good = generate_scheme_tree(hyp, *j);
      if (!good) break;
    }
    if (good)
      schemes.push_back(s);
    else
      delete s;
  }
  unsigned s = schemes.size();
  if (s == 0) {
    bool in_hyp = false;
    for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i) {
      in_hyp = r == i->real;
      if (in_hyp) break;
    }
    if (in_hyp) return true;
    if (graph->has_compatible_hypothesis(r)) return true;
    r->scheme = new no_scheme;
    return false;
  }
  r->scheme = NULL;
  for(unsigned i = 0; i < s; ++i) {
    proof_scheme *p = schemes[i];
    p->next = r->scheme;
    r->scheme = p;
  }
  return true;
}

node *handle_proof(property_vect const &hyp, property &res) {
  typedef std::vector< proof_scheme const * > scheme_stack;
  static scheme_stack st;
  property best_res = res;
  node *best_node = generate_triviality(hyp, best_res);
  graph_storage storage;
  for(proof_scheme const *scheme = res.real->scheme; scheme != NULL; scheme = scheme->next) {
    if (std::count(st.begin(), st.end(), scheme) >= 3) continue; // BLI
    st.push_back(scheme);
    graph_layer layer;
    property res2 = best_res;
    node *n = scheme->generate_proof(hyp, res2);
    if (n && (res2.bnd < best_res.bnd || (!best_node && res2.bnd <= best_res.bnd))) {
      best_node = n;
      best_res = res2;
      layer.store(storage);
    }
    st.pop_back();
  }
  if (best_node) res = best_res;
  return best_node;
}
