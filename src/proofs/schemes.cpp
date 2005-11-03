#include <map>
#include <set>
#include <vector>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/schemes.hpp"

typedef std::set< ast_real const * > ast_real_set;
extern ast_real_set input_reals, output_reals;

struct scheme_factories: std::vector< scheme_factory const * > {
  ~scheme_factories() { for(iterator i = begin(), i_end = end(); i != i_end; ++i) delete *i; }
};
static scheme_factories factories;

struct scheme_factory_wrapper: scheme_factory {
  typedef scheme_register::scheme_factory_fun scheme_factory_fun;
  scheme_factory_fun fun;
  scheme_factory_wrapper(scheme_factory_fun f): fun(f) {}
  virtual proof_scheme *operator()(predicated_real const &r) const
  { return r.pred() == PRED_BND ? (*fun)(r.real()) : NULL; }
};

struct scheme_factorz_wrapper: scheme_factory {
  typedef scheme_register::scheme_factorz_fun scheme_factory_fun;
  scheme_factory_fun fun;
  scheme_factorz_wrapper(scheme_factory_fun f): fun(f) {}
  virtual proof_scheme *operator()(predicated_real const &r) const { return (*fun)(r); }
};

scheme_register::scheme_register(scheme_factory_fun f) {
  factories.push_back(new scheme_factory_wrapper(f));
}

scheme_register::scheme_register(scheme_factorz_fun f) {
  factories.push_back(new scheme_factorz_wrapper(f));
}

scheme_register::scheme_register(scheme_factory const *f) {
  factories.push_back(f);
}

struct dummy_scheme: proof_scheme {
  dummy_scheme(predicated_real const &r): proof_scheme(r) {}
  virtual bool dummy() const { return true; }
  virtual node *generate_proof() const { assert(false); return NULL; }
  virtual preal_vect needed_reals() const { return preal_vect(); }
};

typedef std::set< predicated_real > real_set;
static real_set missing_reals;

typedef std::set< proof_scheme const * > scheme_set;
static scheme_set source_schemes, owned_schemes;

struct real_dependency {
  scheme_set dependent;
  scheme_set schemes;
};
typedef std::map< predicated_real, real_dependency > real_dependencies;
static real_dependencies reals;

static void delete_scheme(proof_scheme const *s, predicated_real const &restricted_real) {
  preal_vect v = s->needed_reals();
  for(preal_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    predicated_real const &real = *i;
    if (real == restricted_real) continue;
    missing_reals.insert(real);
    reals[real].dependent.erase(s);
  }
  delete s;
}

static void initialize_real(predicated_real const &real, proof_scheme const *parent) {
  real_dependencies::iterator it = reals.find(real);
  if (it != reals.end()) {
    it->second.dependent.insert(parent);
    return;
  }
  // no dependencies, let's generate them
  it = reals.insert(std::make_pair(real, real_dependency())).first;
  real_dependency &dep = it->second;
  scheme_set &l = dep.schemes;
  for(scheme_factories::iterator i = factories.begin(), i_end = factories.end(); i != i_end; ++i) {
    proof_scheme *s = (**i)(real);
    if (!s) continue;
    l.insert(s);
  }
  // or an hypothesis?
  if (real.pred() == PRED_BND && input_reals.count(real.real()))
    l.insert(new dummy_scheme(real));
  // create the dependencies
  for(scheme_set::const_iterator i = l.begin(), i_end = l.end(); i != i_end; ++i) {
    proof_scheme const *s = *i;
    preal_vect v = s->needed_reals();
    for(preal_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
      initialize_real(*j, s);
    missing_reals.insert(s->real);
  }
  dep.dependent.insert(parent);
}

ast_real_vect generate_proof_paths() {
  for(ast_real_set::const_iterator i = output_reals.begin(), i_end = output_reals.end(); i != i_end; ++i)
    initialize_real(predicated_real(*i, PRED_BND), NULL);
  for(ast_real_set::const_iterator i = input_reals.begin(), i_end = input_reals.end(); i != i_end; ++i)
    initialize_real(predicated_real(*i, PRED_BND), NULL); // initialize hypothesis reals to handle contradictions
  while (!missing_reals.empty()) {
    predicated_real const &real = *missing_reals.begin();
    real_dependency &r = reals[real];
    if (r.schemes.empty() || r.dependent.empty()) {
      for(scheme_set::const_iterator i = r.dependent.begin(), i_end = r.dependent.end(); i != i_end; ++i) {
        // if we are here, the real has no more scheme, so erase all the schemes that were relying on it
        proof_scheme const *p = *i;
        if (p) // just in case it is a goal real
          delete_scheme(p, real);
      }
      for(scheme_set::const_iterator i = r.schemes.begin(), i_end = r.schemes.end(); i != i_end; ++i) {
        // if we are here, no scheme needs this real anymore, so erase all the schemes of the real
        delete_scheme(*i, predicated_real());
      }
      reals.erase(real);
    }
    missing_reals.erase(real);
  }
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    real_dependency &r = i->second;
    scheme_set v;
    v.swap(r.schemes);
    for(scheme_set::iterator j = v.begin(), j_end = v.end(); j != j_end; ++j) {
      proof_scheme const *s = *j;
      if (s->dummy()) {
        delete_scheme(s, predicated_real());
        continue;
      }
      if (s->needed_reals().empty())
        source_schemes.insert(s);
      r.schemes.insert(s);
    }
    r.dependent.erase(NULL);
  }
  missing_reals.clear();
  ast_real_vect missing_targets;
  for(ast_real_set::iterator i = output_reals.begin(), end = output_reals.end(); i != end; ++i) {
    real_dependencies::iterator j = reals.find(predicated_real(*i, PRED_BND));
    if (j == reals.end())
      missing_targets.push_back(*i);
  }
  return missing_targets;
}

static void insert_dependent(scheme_set &v, predicated_real const &real) {
  real_dependencies::const_iterator i = reals.find(real);
  if (i == reals.end()) return;
  real_dependency const &r = i->second;
  v.insert(r.dependent.begin(), r.dependent.end());
}

node *find_proof(property const &res) {
  node *n = find_proof(res.real);
  return (n && n->get_result().implies(res)) ? n : NULL;
}

bool fill_hypotheses(property *hyp, preal_vect const &v) {
  for(preal_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    node *n = find_proof(*i);
    if (!n) return false;
    *(hyp++) = n->get_result();
  }
  return true;
}

bool graph_t::populate(dichotomy_sequence const &dichotomy) {
  if (contradiction)
    return true;
  graph_loader loader(this);
  typedef std::map< ast_real const *, interval const * > bound_map;
  bound_map bounds;
  bool completely_bounded = true;
  for(property_vect::const_iterator i = goals.begin(), i_end = goals.end(); i != i_end; ++i)
    if (i->real.pred() == PRED_BND && is_defined(i->bnd()))
      bounds[i->real.real()] = &i->bnd();
    else
      completely_bounded = false;
  bound_map::const_iterator bounds_end = bounds.end();
  for(dichotomy_sequence::const_iterator dichotomy_it = dichotomy.begin(),
      dichotomy_end = dichotomy.end(); /*nothing*/; ++dichotomy_it) {
    scheme_set missing_schemes = source_schemes;
    for(node_map::const_iterator i = known_reals.begin(), i_end = known_reals.end(); i != i_end; ++i)
      insert_dependent(missing_schemes, i->first);
    unsigned iter = 0;
    while (iter != 1000000 && !missing_schemes.empty()) {
      ++iter;
      proof_scheme const *s = iter % 16 ? *missing_schemes.begin() : *missing_schemes.rbegin();
      missing_schemes.erase(s);
      node *n = s->generate_proof();
      if (!n || !try_real(n)) continue;
      if (contradiction) return true;
      insert_dependent(missing_schemes, s->real);
      if (s->real.pred() != PRED_BND) continue;
      bound_map::iterator i = bounds.find(s->real.real());
      if (i == bounds_end || !(n->get_result().bnd() <= *i->second)) continue;
      bounds.erase(i);
      if (completely_bounded && bounds.empty()) return false;
      bounds_end = bounds.end();
    }
    if (dichotomy_it == dichotomy_end || !dichotomize(*dichotomy_it))
      return false;
    if (contradiction)
      return true;
  }
}
