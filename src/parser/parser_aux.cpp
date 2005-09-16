#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include <cassert>
#include <iostream>

interval create_interval(ast_interval const &, bool widen);

ast_real const *check_real(ast_ident *v) {
  if (!v->var)
    v->var = normalize(ast_real(v));
  return v->var;
}

ast_prop_and merge_prop_and(ast_prop const &_p1, ast_prop const &_p2) {
  ast_prop_and p;
  if (ast_prop_and const *p1 = boost::get< ast_prop_and const >(&_p1))
    p = *p1;
  else p.push_back(_p1);
  if (ast_prop_and const *p2 = boost::get< ast_prop_and const >(&_p2))
    p.insert(p.end(), p2->begin(), p2->end());
  else p.push_back(_p2);
  return p;
}

static ast_prop_and merge_prop_and(ast_prop const &_p) {
  if (ast_prop_and const *p = boost::get< ast_prop_and const >(&_p))
    return *p;
  else {
    ast_prop_and p;
    p.push_back(_p);
    return p;
  }
}

static property generate_property(ast_atom_bound const &p, bool goal, bool axiom) {
  property r(p.real);
  if (p.interval.lower) {
    assert(p.interval.upper);
    r.bnd = create_interval(p.interval, goal);
  } else {
    if (!goal || axiom)
      { std::cerr << "Error: undefined intervals are reserved for conclusions.\n"; exit(1); }
    assert(!p.interval.upper);
  }
  return r;
}

static void generate_axiom(ast_prop_impl const &p, node_vect &axioms) {
  ast_prop_and tmp = merge_prop_and(p.left);
  property_vect hyp;
  for(int i = 0, l = tmp.size(); i < l; ++i) {
    ast_prop &q = tmp[i];
    if (ast_atom_bound *r = boost::get< ast_atom_bound >(&q))
      hyp.push_back(generate_property(*r, false, true));
    else { std::cerr << "Error: too complex a logical proposition.\n"; exit(1); }
  }
  tmp = merge_prop_and(p.right);
  for(int i = 0, l = tmp.size(); i < l; ++i) {
    if (ast_atom_bound *r = boost::get< ast_atom_bound >(&tmp[i]))
      axioms.push_back(new axiom_node(hyp, generate_property(*r, true, true)));
    else { std::cerr << "Error: too complex a logical proposition.\n"; exit(1); }
  }
}

static void generate_subgraph(ast_prop_impl const &p, node_vect &axioms, property_vect &hyp, property_vect &goal) {
  ast_prop_and tmp = merge_prop_and(p.left);
  for(int i = 0, l = tmp.size(); i < l; ++i) {
    ast_prop &q = tmp[i];
    if (ast_atom_bound *r = boost::get< ast_atom_bound >(&q))
      hyp.push_back(generate_property(*r, false, false));
    else {
      ast_prop_impl *r = boost::get< ast_prop_impl >(&q);
      assert(r);
      generate_axiom(*r, axioms);
    }
  }
  tmp = merge_prop_and(p.right);
  for(int i = 0, l = tmp.size(); i < l; ++i) {
    if (ast_atom_bound *r = boost::get< ast_atom_bound >(&tmp[i]))
      goal.push_back(generate_property(*r, true, false));
    else { std::cerr << "Error: too complex a logical proposition.\n"; exit(1); }
  }
}

std::vector< graph_t * > graphs;

void generate_graph(ast_prop const &p) {
  if (ast_prop_and const *q = boost::get< ast_prop_and >(&p)) {
    for(int i = 0, l = q->size(); i < l; ++i)
      generate_graph((*q)[i]);
  } else {
    ast_prop_impl const *q = boost::get< ast_prop_impl >(&p);
    ast_prop_impl tmp;
    if (!q) {
      tmp.left = ast_prop(ast_prop_and());
      tmp.right = p;
      q = &tmp;
    }
    node_vect axioms;
    property_vect hyp, goal;
    generate_subgraph(*q, axioms, hyp, goal);
    std::set< ast_real const * > real_set;
    for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
      real_set.insert(i->real);
    if (hyp.size() != real_set.size()) // we don't want to encounter: x in [0,2] /\ x in [1,3] -> ...
      { std::cerr << "Error: you don't want to have multiple hypotheses concerning the same real.\n"; exit(1); }
    graph_t *g = new graph_t(NULL, hyp, goal, NULL, true);
    for(node_vect::const_iterator i = axioms.begin(), end = axioms.end(); i != end; ++i)
      g->insert_axiom(*i);
    graphs.push_back(g);
  }
}
