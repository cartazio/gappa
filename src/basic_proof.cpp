#include <iostream>
#include <boost/scoped_array.hpp>
#include "basic_proof.hpp"
#include "proof_graph.hpp"
#include "program.hpp"
#include "ast.hpp"
#include "numbers/interval_ext.hpp"
#include "function.hpp"

node *triviality = new node(OTHER);

struct node_assign: node {
  node_assign(node *n, property const &p): node(OTHER) {
    insert_pred(n);
    res = p;
    hyp = n->hyp;
  }
};

struct node_trivial: node {
  node_trivial(property const &p): node(OTHER) {
    res = p;
    hyp.push_back(p);
  }
};

struct node_reflexive: node {
  node_reflexive(property const &p): node(OTHER) {
    res = p;
  }
};

struct node_modus: node {
  std::string name;
  node_modus(property const &p, node *n, node_vect const &nodes): node(MODUS) {
    res = p;
    insert_pred(n);
    for(node_vect::const_iterator i = nodes.begin(), end = nodes.end(); i != end; ++i)
      if (*i != triviality) insert_pred(*i);
    /* TODO: hypotheses */
  }
};

struct node_plouf: node {
  node_plouf(property_vect const &h, property const &p): node(OTHER) {
    res = p;
    hyp = h;
  }
};

namespace basic_proof {

node *generate_triviality(property_vect const &hyp, property &res) {
  if (node *n = graph->find_compatible_node(hyp, res)) {
    res = n->res;
    return n;
  }
  int i = hyp.find_compatible_property(res);
  if (i < 0) return NULL;
  res = hyp[i];
  return triviality;
}

interval const &compute_triviality(property_vect const &hyp, variable *v) {
  property bnd(PROP_BND);
  bnd.var = v;
  //if (node *n = graph->find_compatible_node(hyp, bnd)) return n->res.bnd;
  int i = hyp.find_compatible_property(bnd);
  if (i < 0) { static interval const not_defined; return not_defined; }
  return hyp[i].bnd;
}

node *generate_bound(property_vect const &hyp, property &res);
node *generate_error(property_vect const &hyp, property &res);

interval compute_bound(property_vect const &hyp, variable *v) {
  { interval const &res = compute_triviality(hyp, v);
    if (is_defined(res)) return res; }
  int idx = v->get_definition();
  if (idx == -1) return interval();
  instruction &inst = program[idx];
  if (!inst.fun) return compute_bound(hyp, inst.in[0]);
  int l = inst.in.size();
  boost::scoped_array< interval > ints_(new interval[l]);
  boost::scoped_array< interval const * > ints(new interval const *[l]);
  for(int i = 0; i < l; ++i) {
    ints_[i] = compute_bound(hyp, inst.in[i]);
    if (!(is_defined(ints_[i]))) return interval();
    ints[i] = &ints_[i];
  }
  return (*inst.fun->bnd_comp->compute)(ints.get());
}

node *generate_bound(property_vect const &hyp, property &res) {
  assert(res.type == PROP_BND);
  if (node *n = generate_triviality(hyp, res)) return n;
  // std::cout << res.var->name->name << " in " << res.bnd << std::endl;
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (!inst.fun) {
    variable *v = res.var;
    res.var = inst.in[0];
    node *n = generate_bound(hyp, res);
    if (!n) return NULL;
    res.var = v;
    return new node_assign(n, res);
  }
  int l = inst.in.size();
  node_vect nodes(l);
  boost::scoped_array< property > props(new property[l]);
  boost::scoped_array< interval const * > ints(new interval const *[l]);
  for(int i = 0; i < l; ++i) {
    props[i].type = PROP_BND;
    props[i].var = inst.in[i];
    if (!(nodes[i] = generate_bound(hyp, props[i]))) return NULL;
    ints[i] = &props[i].bnd;
  }
  interval bnd = (*inst.fun->bnd_comp->compute)(ints.get());
  if (!is_defined(bnd) || !(bnd <= res.bnd)) return NULL;
  res.bnd = bnd;
  node *n = (*inst.fun->bnd_comp->generate)(props.get(), res);
  assert(n);
  return new node_modus(res, n, nodes);
}

node *generate_error_forced(property_vect const &hyp, property &res) {
  assert(res.type == PROP_ABS || res.type == PROP_REL);
  if (node *n = generate_triviality(hyp, res)) return n;
  /*{ static char const *type[] = { "ABS", "REL" };
    std::cout << type[res.error] << '(' << res.var->name->name << ", ...) in " << res.err << std::endl; }*/
  if (variable *const *v = boost::get< variable *const >(res.real))
    if (res.var == *v) {
      res.bnd = interval(interval_real);
      return new node_reflexive(res);
    }
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (!inst.fun) {
    variable *v = res.var;
    res.var = inst.in[0];
    node *n = generate_error(hyp, res);
    if (!n) return NULL;
    res.var = v;
    return new node_assign(n, res);
  }
  real_op const *op = boost::get< real_op const >(res.real);
  if (!op || op->type != inst.fun->type) return NULL;
  node *n = NULL;
  node_vect nodes;
  for(error_computation const *m = inst.fun->err_comp; m->res.var != 0; ++m) {
    if (m->res.var != -1) continue; // TODO
    if (!(m->res.type == HYP_ABS && res.type == PROP_ABS || m->res.type == HYP_REL && res.type == PROP_REL)) continue;
    graph_layer layer;
    bool good = true;
    nodes.clear();
    property_vect props;
    for(hypothesis_constraint const *c = m->constraints; c->var != 0; ++c) {
      variable *v = (c->var < 0) ? inst.out[-1 - c->var] : inst.in[c->var - 1] ;
      node *nn;
      property p;
      p.var = v;
      if (c->type == HYP_BND || c->type == HYP_SNG) {
        p.type = PROP_BND;
        if (!(nn = generate_bound(hyp, p))) { good = false; break; }
        if (c->type == HYP_SNG && !is_singleton(p.bnd)) { good = false; break; }
      } else if (c->type == HYP_ABS || c->type == HYP_REL) {
        p.type = c->type == HYP_ABS ? PROP_ABS : PROP_REL;
        assert(c->var >= 1);
        p.real = &op->ops[c->var - 1];
        if (!(nn = generate_error(hyp, p))) { good = false; break; }
      } else assert(false);
      props.push_back(p);
      nodes.push_back(nn);
    }
    if (!good) continue;
    n = (*m->generate)(props, res);
    if (n) { layer.flatten(); break; }
  }
  if (!n) return NULL;
  return new node_modus(res, n, nodes);
}

node *generate_error(property_vect const &hyp, property &res) {
  assert(res.type == PROP_ABS || res.type == PROP_REL);
  property res2 = res;
  {
    graph_layer layer;
    node *n = generate_error_forced(hyp, res);
    if (n) { layer.flatten(); return n; }
  }
  property bnd(PROP_BND);
  bnd.var = res2.var;
  node *n = generate_bound(hyp, bnd);
  if (!n) return NULL;
  res.type = res2.type == PROP_ABS ? PROP_REL : PROP_ABS;
  res.var = res2.var;
  res.real = res2.real;
  res.bnd = interval();
  n = generate_error_forced(hyp, res);
  if (!n) return NULL;
  res.type = res2.type;
  if (res2.type == PROP_ABS) {
    res.bnd = res.bnd * to_real(bnd.bnd);
    return new node_plouf(hyp, res);
  } else {
    if (!is_zero(res.bnd)) {
      if (contains_zero(bnd.bnd)) return NULL;
      res.bnd = res.bnd / to_real(bnd.bnd);
    }
    return new node_plouf(hyp, res);
  }
}

} // namespace basic_proof

node *generate_basic_proof(property_vect const &hyp, property const &res) {
  property res2 = res;
  node *n;
  if (res.type == PROP_BND)
    n = basic_proof::generate_bound(hyp, res2);
  else
    n = basic_proof::generate_error(hyp, res2);
  assert(n != triviality); // TODO
  return n;
}
