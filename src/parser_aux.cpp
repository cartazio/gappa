#include <cassert>
#include <iostream>
#include "ast.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "property.hpp"
#include "numbers/interval_ext.hpp"

interval create_interval(ast_interval const &, bool widen, type_id);

ast_real *check_real(ast_ident *v) {
  switch (v->id_type) {
  case UNKNOWN_ID:
    { 
      v->id_type = PROG_VAR;
      v->var = new variable(v, UNDEFINED);
    }
    // no break
  case PROG_VAR:
    return v->var->real;
  case REAL_VAR:
    return v->rvar->real;
  default:
    { std::cerr << "Error: " << v->name << " is not a variable\n"; exit(1); }
    return NULL;
  }  
}

variable *check_prog_variable(ast_ident *v, type_id t = UNDEFINED, instruction *ins = NULL) {
  switch (v->id_type) {
  case PROG_VAR:
    if (t != UNDEFINED) {
      if (v->var->type == UNDEFINED) v->var->type = t;
      else if (v->var->type != t)
        { std::cerr << "Error: Type mismatch for " << v->name << '\n'; exit(1); }
    }
    break;
  case UNKNOWN_ID:
    {
      v->id_type = PROG_VAR;
      v->var = new variable(v, t);
    }
    break;
  default:
    { std::cerr << "Error: " << v->name << " is an already defined symbol\n"; exit(1); }
  }
  if (ins != NULL) {
    if (v->var->inst != NULL)
      { std::cerr << "Error: " << v->name << "is assigned more than once\n"; exit(1); }
    v->var->inst = ins;
  }
  return v->var;
}

real_variable *check_real_variable(ast_ident *v, ast_real *r) {
  if (v->id_type != UNKNOWN_ID)
    { std::cerr << "Error: " << v->name << " is an already defined symbol\n"; exit(1); }
  v->id_type = REAL_VAR;
  v->rvar = new real_variable(v, r);
  return v->rvar;
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
  type_id type = interval_real_desc;
  if (variable const *v = r.real->get_variable()) type = v->type;
  if (p.interval.lower) {
    assert(p.interval.upper);
    r.bnd = create_interval(p.interval, (type == interval_real_desc) && goal, type);
  } else assert(!p.interval.upper);
  return r;
}

property generate_property(ast_atom_approx const &p, property **_q) {
  property r(p.ident->real);
  type_id type = p.ident->type;
  assert(type != UNDEFINED);
  ast_interval i = { p.value, p.value };
  r.bnd = create_interval(i, true, type);
  *_q = NULL; /* TODO */
  return r;
}

void generate_subgraph(ast_prop_impl const &p, node_id type) {
  ast_prop_and tmp = merge_prop_and(p.left);
  property_vect hyp;
  for(int i = tmp.size() - 1; i >= 0; i--) {
    ast_prop &q = tmp[i];
    if (ast_atom_bound *r = boost::get< ast_atom_bound >(&q))
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
    ast_atom_bound *r = boost::get< ast_atom_bound >(&q);
    assert(r);
    n->res = generate_property(*r, true);
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
  } else { std::cerr << "Hey!!!\n"; exit(1); }
}

void link_variables() {
  int l = program.size();
  bool restart;
  do {
    restart = false;
    for(int i = l - 1; i >= 0; i--) {
      instruction *ins = program[i];
      variable *v1 = ins->in[0], *v2 = ins->out[0]; // v2=v1 ; if v1 is undefined and v2 is not, propagate to v1
      if (ins->fun != NULL || v1->type != UNDEFINED || v2->type == UNDEFINED) continue;
      v1->type = v2->type;
      restart = true;
    }
  } while (restart);
  make_variables_real();
}
