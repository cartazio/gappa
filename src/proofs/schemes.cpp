#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
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

struct dummy_scheme: proof_scheme {
  ast_real_vect reals;
  dummy_scheme(ast_real const *r, ast_real_vect const &v): proof_scheme(r), reals(v) {}
  virtual bool dummy() const { return true; }
  virtual node *generate_proof() const { assert(false); return NULL; }
  virtual ast_real_vect needed_reals() const { return reals; }
};

static proof_scheme const *get_scheme(ast_real const *real) {
  if (!real->schemes) {
    // no scheme list, let's generate it
    typedef scheme_register all_schemes;
    proof_scheme_list *p = new proof_scheme_list;
    for(all_schemes::iterator i = all_schemes::begin(), i_end = all_schemes::end(); i != i_end; ++i) {
      proof_scheme *s = (**i)(real);
      if (!s) continue;
      p->push_back(s);
    }
    assert(top_graph);
    // maybe there are some axioms?
    node_vect axioms = top_graph->find_useful_axioms(real);
    for(node_vect::const_iterator i = axioms.begin(), i_end = axioms.end(); i != i_end; ++i) {
      property_vect const &hyp = (*i)->get_hypotheses();
      ast_real_vect v;
      for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j)
        v.push_back(j->real);
      p->push_back(new dummy_scheme(real, v));
    }
    // or an hypothesis?
    if (top_graph->find_already_known(real))
      p->push_back(new dummy_scheme(real, ast_real_vect()));
    real->schemes = p;
  }
  proof_scheme_list &l = *real->schemes;
  if (l.empty()) return NULL;
  proof_scheme const *s = l.back();
  l.pop_back();
  return s;
}

static bool find(ast_real_vect &found, ast_real const *r, bool add) {
  ast_real_vect::iterator end = found.end(), i = std::find(found.begin(), end, r);
  if (i != end) return true;
  if (add) found.push_back(r);
  return add;
}

static void revert_schemes(proof_scheme_list &schemes, unsigned from) {
  proof_scheme_list::iterator begin = schemes.begin() + from, end = schemes.end();
  for(proof_scheme_list::iterator i = begin; i != end; ++i)
    (*i)->real->schemes->push_back(*i);
  schemes.erase(begin, end);
}

// FIXME !!!
bool generate_scheme_tree(ast_real const *r, proof_scheme_list &schemes, ast_real_vect &found) {
  // do we already know about this real?
  bool good_real = find(found, r, false);
  if (good_real) return true;
  unsigned from_scheme = schemes.size(), from_real = found.size();
  // let's go through all the (remaining) schemes
  while (proof_scheme const *s = get_scheme(r)) {
    ast_real_vect v = s->needed_reals();
    bool good_scheme = true;
    for(ast_real_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
      good_scheme = generate_scheme_tree(*i, schemes, found);
      if (!good_scheme) break;
    }
    if (!good_scheme) {
      delete s;
      revert_schemes(schemes, from_scheme);
      found.erase(found.begin() + from_real, found.end());
    } else {
      if (!s->dummy())
        schemes.push_back(s);
      if (!good_real) good_real = find(found, r, true);
      from_scheme = schemes.size();
      from_real = found.size();
    }
  }
  // maybe we just found it in an underlying iteration
  if (!good_real) good_real = find(found, r, false);
  return good_real;
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

void proof_handler::operator()() const {
  assert(ordered_schemes);
  typedef std::map< ast_real const *, interval const * > bound_map;
  typedef std::set< ast_real const * > real_set;
  bound_map bounds;
  real_set reals;
  for(property_vect::const_iterator j = goals.begin(), j_end = goals.end(); j != j_end; ++j)
    if (is_defined(j->bnd))
      bounds[j->real] = &j->bnd;
  for(proof_scheme_list::const_iterator j = ordered_schemes->begin(), j_end = ordered_schemes->end(); j != j_end; ++j)
    reals.insert((*j)->real);
  bound_map::const_iterator i_end = bounds.end();
  for(int iter = 0; iter < 3; ++iter) {
    for(real_set::const_iterator j = reals.begin(), j_end = reals.end(); j != j_end; ++j) {
      node_vect axioms = top_graph->find_useful_axioms(*j);
      for(node_vect::const_iterator i = axioms.begin(), i_end = axioms.end(); i != i_end; ++i) {
        node *n = *i;
        property_vect const &hyp = n->get_hypotheses();
        node_vect nodes;
        bool good = true;
        for(property_vect::const_iterator k = hyp.begin(), k_end = hyp.end(); k != k_end; ++k) {
          node *m = find_proof(k->real);
          if (m && m->get_result().bnd <= k->bnd) nodes.push_back(m);
          else { good = false; break; }
        }
        if (!good) continue;
        node *m = new modus_node(nodes.size(), &nodes.front(), n);
        bool b = top_graph->try_real(m);
        assert(b);
        top_graph->remove_axiom(n);
      }
    }
    for(proof_scheme_list::const_iterator j = ordered_schemes->begin(), j_end = ordered_schemes->end(); j != j_end; ++j) {
      proof_scheme const &s = **j;
      graph_layer layer;
      node *n;
      bound_map::const_iterator i = bounds.find(s.real);
      if (i != i_end) n = s.generate_proof(*i->second);
      else n = s.generate_proof();
      if (n && top_graph->try_real(n)) layer.flatten();
    }
  }
}
