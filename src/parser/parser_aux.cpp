#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include <cassert>
#include <iostream>

interval create_interval(ast_interval const &, bool widen);

ast_real const *check_real(ast_ident *v) {
  switch (v->id_type) {
  case UNKNOWN_ID:
    v->id_type = REAL_VAR;
    v->var = normalize(ast_real(v));
    // no break
  case REAL_VAR:
    return v->var;
  default:
    { std::cerr << "Error: " << v->name << " is not a variable\n"; exit(1); }
    return NULL;
  }  
}

void check_variable(ast_ident *v, ast_real const *r) {
  if (v->id_type != UNKNOWN_ID)
    { std::cerr << "Error: " << v->name << " is an already defined symbol\n"; exit(1); }
  v->id_type = REAL_VAR;
  v->var = r;
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

ast_prop_and merge_prop_and(ast_prop const &_p) {
  if (ast_prop_and const *p = boost::get< ast_prop_and const >(&_p))
    return *p;
  else {
    ast_prop_and p;
    p.push_back(_p);
    return p;
  }
}

property generate_property(ast_atom_bound const &p, bool goal) {
  property r(p.real);
  if (p.interval.lower) {
    assert(p.interval.upper);
    r.bnd = create_interval(p.interval, goal);
  } else assert(!p.interval.upper);
  return r;
}

void generate_subgraph(ast_prop_impl const &p, node_id type) {
  ast_prop_and tmp = merge_prop_and(p.left);
  property_vect hyp;
  for(int i = tmp.size() - 1; i >= 0; i--) {
    ast_prop &q = tmp[i];
    if (ast_atom_bound *r = boost::get< ast_atom_bound >(&q))
      hyp.push_back(generate_property(*r, false));
    else {
      ast_prop_impl *r = boost::get< ast_prop_impl >(&q);
      assert(r && type == CONCLUSION);
      generate_subgraph(*r, HYPOTHESIS);
    }
  }
  tmp = merge_prop_and(p.right);
  for(int i = tmp.size() - 1; i >= 0; i--) {
    ast_prop &q = tmp[i];
    node *n = new node(type);
    n->hyp = hyp;
    ast_atom_bound *r = boost::get< ast_atom_bound >(&q);
    assert(r);
    n->res = generate_property(*r, true);
  }
}

void generate_graph(ast_prop const &p) {
  if (ast_prop_impl const *q = boost::get< ast_prop_impl >(&p)) {
    generate_subgraph(*q, CONCLUSION);
  } else if (ast_prop_and const *q = boost::get< ast_prop_and >(&p)) {
    for(int i = q->size() - 1; i >= 0; i--)
      generate_graph((*q)[i]);
  } else {
    ast_prop_impl tmp;
    tmp.right = p;
    generate_subgraph(tmp, CONCLUSION);
  }
}
