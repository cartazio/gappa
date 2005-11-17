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

typedef std::set< predicated_real > real_set;
static real_set missing_reals;

typedef std::set< proof_scheme const * > scheme_set;
static scheme_set source_schemes;

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

static real_dependency &initialize_dependencies(predicated_real const &real) {
  real_dependencies::iterator it = reals.find(real);
  if (it != reals.end()) return it->second;
  // no dependencies yet, let's generate them
  it = reals.insert(std::make_pair(real, real_dependency())).first;
  real_dependency &dep = it->second;
  scheme_set &l = dep.schemes;
  for(scheme_factories::iterator i = factories.begin(), i_end = factories.end(); i != i_end; ++i) {
    proof_scheme *s = (**i)(real);
    if (!s) continue;
    l.insert(s);
  }
  // create the dependencies
  for(scheme_set::const_iterator i = l.begin(), i_end = l.end(); i != i_end; ++i) {
    proof_scheme const *s = *i;
    preal_vect v = s->needed_reals();
    for(preal_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
      initialize_dependencies(*j).dependent.insert(s);
    missing_reals.insert(s->real);
  }
  return it->second;
}

ast_real_vect generate_proof_paths() {
  for(ast_real_set::const_iterator i = output_reals.begin(), i_end = output_reals.end(); i != i_end; ++i)
    initialize_dependencies(predicated_real(*i, PRED_BND)).dependent.insert(NULL);
  // initialize hypothesis reals to handle contradictions
  for(ast_real_set::const_iterator i = input_reals.begin(), i_end = input_reals.end(); i != i_end; ++i)
    initialize_dependencies(predicated_real(*i, PRED_BND)).schemes.insert(NULL);
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
        proof_scheme const *p = *i;
        if (p) // just in case it is a hypothesis real
          delete_scheme(p, predicated_real());
      }
      reals.erase(real);
    }
    missing_reals.erase(real);
  }
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    real_dependency &r = i->second;
    r.schemes.erase(NULL);
    for(scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j) {
      proof_scheme const *s = *j;
      if (s->needed_reals().empty())
        source_schemes.insert(s);
    }
    r.dependent.erase(NULL);
  }
  ast_real_vect missing_targets;
  for(ast_real_set::iterator i = output_reals.begin(), end = output_reals.end(); i != end; ++i) {
    real_dependencies::iterator j = reals.find(predicated_real(*i, PRED_BND));
    if (j == reals.end())
      missing_targets.push_back(*i);
  }
  return missing_targets;
}

#ifdef LEAK_CHECKER
struct proof_paths_cleaner {
  ~proof_paths_cleaner();
};

proof_paths_cleaner::~proof_paths_cleaner() {
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    scheme_set &s = i->second.schemes;
    for(scheme_set::iterator j = s.begin(), j_end = s.end(); j != j_end; ++j)
      delete *j;
  }
}

static proof_paths_cleaner dummy;
#endif // LEAK_CHECKER

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

bool graph_t::populate(property_tree const &goals, dichotomy_sequence const &dichotomy) {
  if (contradiction)
    return true;
  property_tree current_goals = goals;
  graph_loader loader(this);
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
      if (!n || !try_real(n)) continue;		// the scheme did not find anything useful
      if (contradiction) return true;		// we have got a contradiction, everything is true
      insert_dependent(missing_schemes, s->real);
      if (current_goals.empty()) continue;	// originally empty, we are striving for a contradiction
      if (s->real.pred() != PRED_BND) continue;
      current_goals.remove(n->get_result());
      if (current_goals.empty()) return false;	// now empty, there is nothing left to prove
    }
    if (dichotomy_it == dichotomy_end || !dichotomize(current_goals, *dichotomy_it))
      return false;
    if (contradiction)
      return true;
  }
}
