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

struct no_scheme: proof_scheme {
  virtual node *generate_proof(ast_real const *) const { return NULL; }
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
};

struct yes_scheme: proof_scheme {
  virtual node *generate_proof(ast_real const *) const { return NULL; }
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
};

bool generate_scheme_tree(ast_real const *r, ast_real_vect &reals, ast_real_vect &discarded) {
  if (r->scheme) {
    bool b = !dynamic_cast< no_scheme const * >(r->scheme);
    if (b) {
      ast_real_vect::iterator end = discarded.end(), i = std::find(discarded.begin(), end, r);
      if (i == end) return true;
      reals.push_back(r);
      discarded.erase(i);
    }
    return b;
  }
  // put a dummy yes_scheme as a marker for the current real
  r->scheme = new yes_scheme;
  std::vector< proof_scheme * > schemes;
  unsigned last_real = reals.size(), last_real_tmp = last_real;
  int need_self_tristate = 1;
  typedef scheme_register all_schemes;
  for(all_schemes::iterator i = all_schemes::begin(), i_end = all_schemes::end(); i != i_end; ++i) {
    proof_scheme *s = (**i)(r);
    if (!s) continue;
    ast_real_vect v = s->needed_reals(r);
    bool good = true, need_self = false;
    for(ast_real_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j) {
      if (*j == r) need_self = true;
      good = generate_scheme_tree(*j, reals, discarded);
      if (!good) break;
    }
    if (good) {
      schemes.push_back(s);
      last_real = reals.size();
      if (!need_self) need_self_tristate = 0;
      else if (need_self_tristate == 1) need_self_tristate = 2;
    } else {
      delete s;
      discarded.insert(discarded.end(), reals.begin() + last_real, reals.end());
      reals.erase(reals.begin() + last_real, reals.end());
    }
  }
  if (need_self_tristate == 2) { // only self-referencing schemes, no interesting one
    for(std::vector< proof_scheme * >::iterator i = schemes.begin(), end = schemes.end(); i != end; ++i)
      delete *i;
    schemes.clear();
    discarded.insert(discarded.end(), reals.begin() + last_real_tmp, reals.end());
    reals.erase(reals.begin() + last_real_tmp, reals.end());
    last_real = last_real_tmp;
  }
  bool in_hyp = false;
  {
    assert(top_graph);
    node_vect axioms = top_graph->find_useful_axioms(r);
    for(node_vect::const_iterator i = axioms.begin(), i_end = axioms.end(); i != i_end; ++i) {
      property_vect const &hyp = (*i)->get_hypotheses();
      bool good = true;
      for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j) {
        good = generate_scheme_tree(j->real, reals, discarded);
        if (!good) break;
      }
      if (good) {
        last_real = reals.size();
        in_hyp = true;
      } else {
        discarded.insert(discarded.end(), reals.begin() + last_real, reals.end());
        reals.erase(reals.begin() + last_real, reals.end());
      }
    }
  }
  if (node *n = top_graph->find_already_known(r)) {
    property_vect const &hyp = n->get_hypotheses();
    bool good = true;
    for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j) {
      good = generate_scheme_tree(j->real, reals, discarded);
      if (!good) break;
    }
    if (good) {
      last_real = reals.size();
      in_hyp = true;
    } else {
      discarded.insert(discarded.end(), reals.begin() + last_real, reals.end());
      reals.erase(reals.begin() + last_real, reals.end());
    }
  }
  unsigned s = schemes.size();
  if (s == 0) {
    if (!in_hyp) {
      property_vect const &hyp = top_graph->get_hypotheses();
      for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i) {
        in_hyp = r == i->real;
        if (in_hyp) break;
      }
    }
    if (in_hyp) {
      // keep the dummy yes_scheme as a marker for an already done real
      // without any non-trivial scheme
      goto keep_it;
    }
    delete r->scheme;
    // put a dummy no_scheme to mark this real as unusable
    r->scheme = new no_scheme;
    return false;
  }
  delete r->scheme;
  r->scheme = NULL;
  for(unsigned i = 0; i < s; ++i) {
    proof_scheme *p = schemes[i];
    p->next = r->scheme;
    r->scheme = p;
  }
 keep_it:
  reals.push_back(r);
  return true;
}

node *proof_scheme::generate_proof(property const &res) const {
  return generate_proof(res.real);
}

node *find_proof(ast_real const *real) {
  return top_graph->find_already_known(real);
}

void handle_proof(property const &res) {
  for(proof_scheme const *scheme = res.real->scheme; scheme != NULL; scheme = scheme->next) {
    graph_layer layer;
    node *n = scheme->generate_proof(res);
    if (n && top_graph->try_real(n)) layer.flatten();
  }
}

void handle_proof(ast_real const *real) {
  for(proof_scheme const *scheme = real->scheme; scheme != NULL; scheme = scheme->next) {
    graph_layer layer;
    node *n = scheme->generate_proof(real);
    if (n && top_graph->try_real(n)) layer.flatten();
  }
  node_vect axioms = top_graph->find_useful_axioms(real);
  for(node_vect::const_iterator i = axioms.begin(), i_end = axioms.end(); i != i_end; ++i) {
    node *n = *i;
    property_vect const &hyp = n->get_hypotheses();
    node_vect nodes;
    bool good = true;
    for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j) {
      node *m = find_proof(j->real);
      if (m && m->get_result().bnd <= j->bnd) nodes.push_back(m);
      else { good = false; break; }
    }
    if (!good) continue;
    node *m = new modus_node(nodes.size(), &nodes.front(), n);
    bool b = top_graph->try_real(m);
    assert(b);
    top_graph->remove_axiom(n);
  }
}
  
node *find_proof(property const &res) {
  node *n = find_proof(res.real);
  return (n && n->get_result().bnd <= res.bnd) ? n : NULL;
}

void proof_handler::operator()() const {
  assert(ordered_reals);
  for(int iter = 0; iter < 3; ++iter) {
    for(ast_real_vect::const_iterator j = ordered_reals->begin(), j_end = ordered_reals->end(); j != j_end; ++j)
      handle_proof(*j);
    for(property_vect::const_iterator j = goals.begin(), j_end = goals.end(); j != j_end; ++j)
      handle_proof(*j);
  }
}
