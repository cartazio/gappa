#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/schemes.hpp"

#include <iostream>
#include <map>
#include <set>

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

struct dummy_scheme: proof_scheme {
  ast_real_vect reals;
  dummy_scheme(ast_real const *r, ast_real_vect const &v): proof_scheme(r), reals(v) {}
  virtual bool dummy() const { return true; }
  virtual node *generate_proof() const { assert(false); return NULL; }
  virtual ast_real_vect needed_reals() const { return reals; }
};

struct proof_helper {
  typedef std::set< ast_real const * > real_set;
  real_set missing_reals;
  real_set axiom_reals;

  typedef std::set< proof_scheme const * > scheme_set;
  scheme_set source_schemes;
  scheme_set owned_schemes;

  struct real_dependency {
    scheme_set dependent;
    scheme_set schemes;
  };
  typedef std::map< ast_real const *, real_dependency > real_dependencies;
  real_dependencies reals;
  void initialize_real(ast_real const *, proof_scheme const *);
  void delete_scheme(proof_scheme const *, ast_real const *);

  proof_helper(ast_real_vect &);
  proof_helper(proof_helper const &);
  ~proof_helper();

  void insert_dependent(scheme_set &, ast_real const *) const;
};

void proof_helper::initialize_real(ast_real const *real, proof_scheme const *parent) {
  real_dependencies::iterator it = reals.find(real);
  if (it != reals.end()) {
    it->second.dependent.insert(parent);
    return;
  }
  // no dependencies, let's generate them
  it = reals.insert(std::make_pair(real, real_dependency())).first;
  real_dependency &dep = it->second;
  scheme_set &l = dep.schemes;
  typedef scheme_register all_schemes;
  for(all_schemes::iterator i = all_schemes::begin(), i_end = all_schemes::end(); i != i_end; ++i) {
    proof_scheme *s = (**i)(real);
    if (!s) continue;
    l.insert(s);
  }
  assert(top_graph);
  // maybe there are some axioms?
  node_vect axioms = top_graph->find_useful_axioms(real);
  for(node_vect::const_iterator i = axioms.begin(), i_end = axioms.end(); i != i_end; ++i) {
    property_vect const &hyp = (*i)->get_hypotheses();
    ast_real_vect v;
    for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j)
      v.push_back(j->real);
    l.insert(new dummy_scheme(real, v));
  }
  // or an hypothesis?
  if (top_graph->find_already_known(real))
    l.insert(new dummy_scheme(real, ast_real_vect()));
  // create the dependencies
  for(scheme_set::const_iterator i = l.begin(), i_end = l.end(); i != i_end; ++i) {
    proof_scheme const *s = *i;
    ast_real_vect v = s->needed_reals();
    for(ast_real_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
      initialize_real(*j, s);
    missing_reals.insert(s->real);
  }
  dep.dependent.insert(parent);
}

void proof_helper::delete_scheme(proof_scheme const *s, ast_real const *restricted_real) {
  ast_real_vect v = s->needed_reals();
  for(ast_real_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    ast_real const *real = *i;
    if (real == restricted_real) continue;
    missing_reals.insert(real);
    reals[real].dependent.erase(s);
  }
  delete s;
}

proof_helper::proof_helper(ast_real_vect &targets) {
  for(ast_real_vect::const_iterator i = targets.begin(), i_end = targets.end(); i != i_end; ++i)
    initialize_real(*i, NULL);
  assert(top_graph);
  property_vect const &hyp = top_graph->get_hypotheses();
  for(property_vect::const_iterator i = hyp.begin(), i_end = hyp.end(); i != i_end; ++i)
    initialize_real(i->real, NULL); // initialize hypothesis reals to handle contradictions
  while (!missing_reals.empty()) {
    ast_real const *real = *missing_reals.begin();
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
        delete_scheme(*i, NULL);
      }
      axiom_reals.erase(real);
      reals.erase(real);
    }
    missing_reals.erase(real);
  }
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    ast_real const *real = i->first;
    real_dependency &r = i->second;
    scheme_set v;
    v.swap(r.schemes);
    for(scheme_set::iterator j = v.begin(), j_end = v.end(); j != j_end; ++j) {
      proof_scheme const *s = *j;
      if (s->dummy()) {
        axiom_reals.insert(real);
        delete_scheme(s, NULL);
        continue;
      }
      if (s->needed_reals().empty())
        source_schemes.insert(s);
      r.schemes.insert(s);
    }
    r.dependent.erase(NULL);
  }
  missing_reals.clear();
  for(ast_real_vect::iterator i = targets.begin(), end = targets.end(); i != end; ++i) {
    real_dependencies::iterator j = reals.find(*i);
    if (j == reals.end())
      *i = NULL;
  }
}

proof_helper::proof_helper(proof_helper const &h)
  : axiom_reals(h.axiom_reals), source_schemes(h.source_schemes), reals(h.reals) {
}

proof_helper::~proof_helper() {
  for(scheme_set::iterator j = owned_schemes.begin(), j_end = owned_schemes.end(); j != j_end; ++j)
    delete *j;
}

void proof_helper::insert_dependent(scheme_set &v, ast_real const *real) const {
  real_dependencies::const_iterator i = reals.find(real);
  if (i == reals.end()) return;
  real_dependency const &r = i->second;
  v.insert(r.dependent.begin(), r.dependent.end());
}

proof_helper *generate_proof_helper(ast_real_vect &reals) {
  return new proof_helper(reals);
}

proof_helper *duplicate_proof_helper(proof_helper const *h) {
  if (!h) return NULL;
  return new proof_helper(*h);
}

void delete_proof_helper(proof_helper *h) {
  delete h;
}

node *proof_scheme::generate_proof(interval const &) const {
  return generate_proof();
}

node *find_proof(ast_real const *real) {
  return top_graph->find_already_known(real);
}

node *find_proof(property const &res) {
  node *n = find_proof(res.real);
  return (n && n->get_result().bnd <= res.bnd) ? n : NULL;
}

bool graph_t::populate() {
  graph_loader loader(this);
  typedef proof_helper::real_set real_set;
  typedef std::map< ast_real const *, interval const * > bound_map;
  bound_map bounds;
  bool completely_bounded = true;
  for(property_vect::const_iterator i = goals.begin(), i_end = goals.end(); i != i_end; ++i)
    if (is_defined(i->bnd))
      bounds[i->real] = &i->bnd;
    else
      completely_bounded = false;
  bound_map::const_iterator bounds_end = bounds.end();
  proof_helper::scheme_set missing_schemes = helper->source_schemes;
  for(node_map::const_iterator i = known_reals.begin(), i_end = known_reals.end(); i != i_end; ++i)
    helper->insert_dependent(missing_schemes, i->first);
  int iter = 0;
  while (iter != 1000000 && !missing_schemes.empty()) {
    ++iter;
    proof_scheme const *s = *missing_schemes.begin();
    missing_schemes.erase(s);
    bound_map::const_iterator i = bounds.find(s->real);
    node *n;
    if (i != bounds_end) n = s->generate_proof(*i->second);
    else n = s->generate_proof();
    if (n && try_real(n)) {
      if (top_graph->get_contradiction()) break;
      helper->insert_dependent(missing_schemes, s->real);
    }
    if (completely_bounded && n && i != bounds_end && n->get_result().bnd <= *i->second) {
      bounds.erase(s->real);
      if (bounds.empty()) break;
      bounds_end = bounds.end();
    }
    real_set v;
    v.swap(helper->axiom_reals);
    for(real_set::iterator i = v.begin(), i_end = v.end(); i != i_end; ++i) {
      ast_real const *real = *i;
      node_vect axioms = find_useful_axioms(real);
      for(node_vect::const_iterator j = axioms.begin(), j_end = axioms.end(); j != j_end; ++j) {
        node *n = *j;
        property_vect const &hyp = n->get_hypotheses();
        bool good = true;
        for(property_vect::const_iterator k = hyp.begin(), k_end = hyp.end(); k != k_end; ++k)
          if (!find_proof(*k)) { good = false; break; }
        if (!good) {
          helper->axiom_reals.insert(real);
          continue;
        }
        node *m = create_modus(n);
        bool b = try_real(m);
        assert(b);
        remove_axiom(n);
        helper->insert_dependent(missing_schemes, real);
      }
    }
  }
  if (owned_helper)
    delete helper;
  helper = NULL;
  return get_contradiction();
}
