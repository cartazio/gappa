#include "basic_proof.hpp"
#include "proof_graph.hpp"
#include "program.hpp"
#include "ast.hpp"
#include "interval.hpp"
#include <iostream>

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
  node_reflexive(variable *v, int e): node(OTHER) {
    property_error p;
    p.var = v;
    p.real = v->real;
    p.err = interval(interval_variant(interval_real()));
    p.error = e;
    res = p;
  }
};

struct node_plouf: node {
  node_plouf(property_vect const &h, property const &p): node(OTHER) {
    res = p;
    hyp = h;
  }
};

struct do_generate_basic_proof: boost::static_visitor< node * > {
  property_vect const &hyp;
  do_generate_basic_proof(property_vect const &h): hyp(h) {}
  node *operator()(property_bound const &res) const;
  node *operator()(property_error const &res) const;
};

node *do_generate_basic_proof::operator()(property_bound const &res) const {
  //std::cout << resb->var->name->name << " in " << resb->bnd << std::endl;
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (inst.fun == NULL) {
    property_bound p = res;
    p.var = inst.in[0];
    node *n = generate_basic_proof(hyp, p);
    if (!n) return NULL;
    property_bound *r = boost::get< property_bound >(&n->res);
    assert(r);
    p = *r;
    p.var = res.var;
    return new node_assign(n, p);
  }
  int l = inst.in.size();
  node_vect nodes;
  for(int i = 0; i < l; i++) {
    property_bound p;
    p.var = inst.in[i];
    node *n = generate_basic_proof(hyp, p);
    if (!n) return NULL;
    nodes.push_back(n);
  }
  assert(l == 2);
  property_bound *lhs = boost::get< property_bound >(&nodes[0]->res);
  property_bound *rhs = boost::get< property_bound >(&nodes[1]->res);
  assert(lhs && rhs);
  property_bound p = res;
  if (inst.fun->name->name == "add32") p.bnd = lhs->bnd + rhs->bnd;
  else if (inst.fun->name->name == "mul32") p.bnd = lhs->bnd * rhs->bnd;
  else assert(false);
  //if (!(p > res)) return NULL;
  return new node_plouf(hyp, p);
}

node *do_generate_basic_proof::operator()(property_error const &res) const {
  //static char const *type[] = { "ABS", "REL" };
  //std::cout << type[rese->error] << '(' << rese->var->name->name << ", " << *rese->real << ") in " << rese->err << std::endl;
  if (variable *const *v = boost::get< variable *const >(res.real))
    if (res.var == *v) return new node_reflexive(res.var, res.error);
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (inst.fun == NULL) {
    property_error p = res;
    p.var = inst.in[0];
    node *n = generate_basic_proof(hyp, p);
    if (!n) return NULL;
    property_error *r = boost::get< property_error >(&n->res);
    assert(r);
    p = *r;
    p.var = res.var;
    return new node_assign(n, p);
  }
  if (res.error != 0) return NULL;
  int l = inst.in.size();
  if (unary_op const *o = boost::get< unary_op const >(res.real)) {
    if (l != 1 || o->type != inst.fun->real_op) return NULL;
    /* TODO */
    return NULL;
  }
  if (binary_op const *o = boost::get< binary_op const >(res.real)) {
    if (l != 2 || o->type != inst.fun->real_op) return NULL;
    property_bound pb;
    property_error pe;
    pe.error = 0;
    if (inst.fun->name->name == "add32") {
      node *n_lhs, *n_rhs, *nb_res;
      pe.var = inst.in[0];
      pe.real = &o->left;
      if (!(n_lhs = generate_basic_proof(hyp, pe))) return NULL;
      property_error *p_lhs = boost::get< property_error >(&n_lhs->res);
      pe.var = inst.in[1];
      pe.real = &o->right;
      if (!(n_rhs = generate_basic_proof(hyp, pe))) return NULL;
      property_error *p_rhs = boost::get< property_error >(&n_rhs->res);
      pb.var = inst.out[0];
      if (!(nb_res = generate_basic_proof(hyp, pb))) return NULL;
      property_bound *pb_res = boost::get< property_bound >(&nb_res->res);
      assert(p_lhs && p_rhs && p_lhs->error == 0 && p_rhs->error == 0 && pb_res);
      property_error p = res;
      p.err = p_lhs->err + p_rhs->err + from_exponent(ulp_exponent(pb_res->bnd), GMP_RNDN);
      return new node_plouf(hyp, p);
    }
    if (inst.fun->name->name == "mul32") {
      node *nb_lhs, *nb_rhs, *nb_res, *ne_lhs, *ne_rhs;
      pe.var = inst.in[0];
      pe.real = &o->left;
      if (!(ne_lhs = generate_basic_proof(hyp, pe))) return NULL;
      property_error *pe_lhs = boost::get< property_error >(&ne_lhs->res);
      pe.var = inst.in[1];
      pe.real = &o->right;
      if (!(ne_rhs = generate_basic_proof(hyp, pe))) return NULL;
      property_error *pe_rhs = boost::get< property_error >(&ne_rhs->res);
      pb.var = inst.in[0];
      if (!(nb_lhs = generate_basic_proof(hyp, pb))) return NULL;
      property_bound *pb_lhs = boost::get< property_bound >(&nb_lhs->res);
      pb.var = inst.in[1];
      if (!(nb_rhs = generate_basic_proof(hyp, pb))) return NULL;
      property_bound *pb_rhs = boost::get< property_bound >(&nb_rhs->res);
      pb.var = inst.out[0];
      if (!(nb_res = generate_basic_proof(hyp, pb))) return NULL;
      property_bound *pb_res = boost::get< property_bound >(&nb_res->res);
      assert(pe_lhs && pe_rhs && pe_lhs->error == 0 && pe_rhs->error == 0 && pb_lhs && pb_rhs && pb_res);
      property_error p = res;
      p.err = pe_lhs->err * to_real(pb_rhs->bnd) + pe_rhs->err * to_real(pb_lhs->bnd)
            + pe_lhs->err * pe_rhs->err + from_exponent(ulp_exponent(pb_res->bnd), GMP_RNDN);
      return new node_plouf(hyp, p);
    }
  }
  assert(false);
  return NULL;
}

node *generate_basic_proof(property_vect const &hyp, property const &res) {
  if (node *n = graph->find_compatible_node(hyp, res)) return n;
  int i = hyp.find_compatible_property(res);
  if (i >= 0) return new node_trivial(hyp[i]);
  return boost::apply_visitor(do_generate_basic_proof(hyp), res);
}
