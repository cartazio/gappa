#include <iostream>
#include "basic_proof.hpp"
#include "proof_graph.hpp"
#include "program.hpp"
#include "ast.hpp"
#include "interval.hpp"
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
  node_reflexive(property_error const &p): node(OTHER) {
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

template< class T >
node *generate_triviality(property_vect const &hyp, T &res) {
  if (node *n = graph->find_compatible_node(hyp, res)) {
    T *p = boost::get< T >(&n->res);
    assert(p);
    res = *p;
    return n;
  }
  int i = hyp.find_compatible_property(res);
  if (i < 0) return NULL;
  T const *p = boost::get< T const >(&hyp[i]);
  assert(p);
  res = *p;
  return triviality;
}

struct do_generate_basic_proof: boost::static_visitor< node * > {
  property_vect const &hyp;
  do_generate_basic_proof(property_vect const &h): hyp(h) {}
  node *operator()(property_bound const &res) const;
  node *operator()(property_error const &res) const;
};

node *generate_basic_proof_bound(property_vect const &hyp, property_bound &res);
node *generate_basic_proof_error(property_vect const &hyp, property_error &res);

node *generate_basic_proof_bound(property_vect const &hyp, property_bound &res) {
  if (node *n = generate_triviality(hyp, res)) return n;
  // std::cout << res.var->name->name << " in " << res.bnd << std::endl;
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (inst.fun == NULL) {
    variable *v = res.var;
    res.var = inst.in[0];
    node *n = generate_basic_proof_bound(hyp, res);
    if (!n) return NULL;
    res.var = v;
    return new node_assign(n, res);
  }
  node *n = NULL;
  node_vect nodes;
  for(function_match *m = inst.fun->matches; m->res.var != 0; ++m) {
    if (m->res.var != -1) continue; /* TODO */
    if (m->res.type != HYP_BND) continue;
    graph_layer layer;
    bool good = true;
    nodes.clear();
    property_vect props;
    for(hypothesis_constraint *c = m->constraints; c->var != 0; ++c) {
      variable *v = (c->var < 0) ? inst.out[-1 - c->var] : inst.in[c->var - 1] ;
      node *nn;
      if (c->type == HYP_BND) {
        property_bound p;
        p.var = v;
        if (!(nn = generate_basic_proof_bound(hyp, p))) { good = false; break; }
        props.push_back(p);
      } else assert(false);
      nodes.push_back(nn);
    }
    if (!good) continue;
    n = (*m->generate_bound)(props, res);
    if (n != NULL) { layer.flatten(); break; }
  }
  if (n == NULL) return NULL;
  return new node_modus(res, n, nodes);
}

node *generate_basic_proof_error(property_vect const &hyp, property_error &res) {
  if (node *n = generate_triviality(hyp, res)) return n;
  /*{ static char const *type[] = { "ABS", "REL" };
    std::cout << type[res.error] << '(' << res.var->name->name << ", " << res.real << ") in " << res.err << std::endl; }*/
  if (variable *const *v = boost::get< variable *const >(res.real))
    if (res.var == *v) {
      res.err = interval(interval_variant(interval_real()));
      return new node_reflexive(res);
    }
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (inst.fun == NULL) {
    variable *v = res.var;
    res.var = inst.in[0];
    node *n = generate_basic_proof_error(hyp, res);
    if (!n) return NULL;
    res.var = v;
    return new node_assign(n, res);
  }
  if (res.error != 0) return NULL; // TODO
  node *n = NULL;
  node_vect nodes;
  for(function_match *m = inst.fun->matches; m->res.var != 0; ++m) {
    if (m->res.var != -1) continue; /* TODO */
    if (m->res.type != HYP_ABS) continue;
    graph_layer layer;
    bool good = true;
    nodes.clear();
    property_vect props;
    for(hypothesis_constraint *c = m->constraints; c->var != 0; ++c) {
      variable *v = (c->var < 0) ? inst.out[-1 - c->var] : inst.in[c->var - 1] ;
      node *nn;
      if (c->type == HYP_BND) {
        property_bound p;
        p.var = v;
        if (!(nn = generate_basic_proof_bound(hyp, p))) { good = false; break; }
        props.push_back(p);
      } else if (c->type == HYP_ABS) {
        property_error p;
        p.var = v;
        p.error = 0;
        binary_op const *o = boost::get< binary_op const >(res.real); // TODO
        assert(o);
        p.real = (c->var == 1) ? &o->left : &o->right;
        if (!(nn = generate_basic_proof_error(hyp, p))) { good = false; break; }
        props.push_back(p);
      } else assert(false);
      nodes.push_back(nn);
    }
    if (!good) continue;
    n = (*m->generate_error)(props, res);
    if (n != NULL) { layer.flatten(); break; }
  }
  if (n == NULL) return NULL;
  return new node_modus(res, n, nodes);
}

node *do_generate_basic_proof::operator()(property_bound const &res) const {
  property_bound res2 = res;
  node *n = generate_basic_proof_bound(hyp, res2);
  assert(n != triviality); // TODO
  return n;
}

node *do_generate_basic_proof::operator()(property_error const &res) const {
  property_error res2 = res;
  node *n = generate_basic_proof_error(hyp, res2);
  assert(n != triviality); // TODO
  return n;
}

node *generate_basic_proof(property_vect const &hyp, property const &res) {
  return boost::apply_visitor(do_generate_basic_proof(hyp), res);
}
