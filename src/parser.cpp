#include <cassert>
#include <iostream>
#include "ast.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "property.hpp"
#include "numbers/interval_ext.hpp"

interval create_interval(ast_interval const &, bool widen, type_id = UNDEFINED);

variable *check_variable(ast_ident *v, type_id t = UNDEFINED) {
  if (v->fun)
    { std::cerr << "Error: " << v->name << " is a function symbol" << std::endl; exit(1); }
  if (!v->var) v->var = new variable(v, t);
  else if (t != UNDEFINED) {
    if (v->var->type == UNDEFINED) v->var->type = t;
    else if (v->var->type != t)
      { std::cerr << "Error: Type mismatch for " << v->name << std::endl; exit(1); }
  }
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

ast_prop_and merge_prop_and(ast_prop const &_p) {
  if (ast_prop_and const *p = boost::get< ast_prop_and const >(&_p))
    return *p;
  else {
    ast_prop_and p;
    p.push_back(_p);
    return p;
  }
}

property generate_property(ast_atom_bound const &p) {
  property r(PROP_BND);
  r.var = p.ident;
  type_id type = r.var->type;
  assert(type != UNDEFINED);
  if (p.interval) {
    r.bnd = create_interval(*p.interval, false, type);
    delete p.interval;
  }
  return r;
}

property generate_property(ast_atom_error const &p, bool goal) {
  property r(p.error == 0 ? PROP_ABS : PROP_REL);
  r.var = p.ident;
  r.real = p.real;
  if (p.interval) {
    r.bnd = create_interval(*p.interval, goal);
    delete p.interval;
  }
  return r;
}

typedef std::pair< property, property > property_pair;

property generate_property(ast_atom_approx const &p, property **_q) {
  property r(PROP_BND);
  r.var = p.ident;
  type_id type = r.var->type;
  assert(type != UNDEFINED);
  ast_interval i(p.value, p.value);
  r.bnd = create_interval(i, false, type);
  *_q = NULL; /* TODO */
  return r;
}

void generate_subgraph(ast_prop_impl const &p, node_id type) {
  ast_prop_and tmp = merge_prop_and(p.left);
  property_vect hyp;
  for(int i = tmp.size() - 1; i >= 0; i--) {
    ast_prop &q = tmp[i];
    if (ast_atom_bound *r = boost::get< ast_atom_bound >(&q))
      hyp.push_back(generate_property(*r));
    else if (ast_atom_error *r = boost::get< ast_atom_error >(&q))
      hyp.push_back(generate_property(*r, false));
    else if (ast_atom_approx *r = boost::get< ast_atom_approx >(&q)) {
      property *s;
      hyp.push_back(generate_property(*r, &s));
      if (s) { hyp.push_back(*s); delete s; }
    } else {
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
    if (ast_atom_bound *r = boost::get< ast_atom_bound >(&q))
      n->res = generate_property(*r);
    else if (ast_atom_error *r = boost::get< ast_atom_error >(&q))
      n->res = generate_property(*r, true);
    else assert(false);
  }
}

void generate_graph(ast_prop const &p, ast_prop_and const &r) {
  if (ast_prop_impl const *q = boost::get< ast_prop_impl >(&p)) {
    ast_prop_impl tmp;
    tmp.left = merge_prop_and(q->left, r);
    tmp.right = q->right;
    generate_subgraph(tmp, CONCLUSION);
  } else if (ast_prop_and const *q = boost::get< ast_prop_and >(&p)) {
    for(int i = q->size() - 1; i >= 0; i--)
      generate_graph((*q)[i], r);
  } else { std::cerr << "Hey!!!"; exit(1); }
}

void link_variables() {
  int l = program.size();
  bool restart;
  do {
    restart = false;
    for(int i = l - 1; i >= 0; i--) {
      instruction &ins = program[i];
      variable *v1 = ins.in[0], *v2 = ins.out[0]; // v2=v1 ; if v1 is undefined and v2 is not, propagate to v1
      if (ins.fun != NULL || v1->type != UNDEFINED || v2->type == UNDEFINED) continue;
      v1->type = v2->type;
      restart = true;
    }
  } while (restart);
  make_variables_real();
}
