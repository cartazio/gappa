#include "basic_proof.hpp"
#include "proof_graph.hpp"
#include "program.hpp"
#include "ast.hpp"
#include "interval.hpp"
#include <iostream>

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

struct node_theorem: node {
  std::string name;
  node_theorem(property_vect const &h, property const &p, std::string const &n): node(THEOREM) {
    res = p;
    hyp = h;
    name = n;
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
  int l = inst.in.size();
  std::vector< node * > nodes(l);
  std::vector< property > props(l);
  for(int i = 0; i < l; i++) {
    property_bound p;
    p.var = inst.in[i];
    if (!(nodes[i] = generate_basic_proof_bound(hyp, p))) return NULL;
    props[i] = p;
  }
  assert(l == 2);
  property_bound *lhs = boost::get< property_bound >(&props[0]);
  property_bound *rhs = boost::get< property_bound >(&props[1]);
  assert(lhs && rhs);
  if (inst.fun->name->name == "add32") res.bnd = lhs->bnd + rhs->bnd;
  else if (inst.fun->name->name == "mul32") res.bnd = lhs->bnd * rhs->bnd;
  else assert(false);
  //if (!(p > res)) return NULL;
  property_vect hyp2;
  hyp2.push_back(*lhs);
  hyp2.push_back(*rhs);
  node *n = new node_theorem(hyp2, res, inst.fun->name->name);
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
  if (res.error != 0) return NULL; /* TODO */
  int l = inst.in.size();
  if (unary_op const *o = boost::get< unary_op const >(res.real)) {
    if (l != 1 || o->type != inst.fun->real_op) return NULL;
    /* TODO */
    return NULL;
  }
  if (binary_op const *o = boost::get< binary_op const >(res.real)) {
    if (l != 2 || o->type != inst.fun->real_op) return NULL;
    property_error pe_lhs, pe_rhs;
    pe_lhs.error = 0;
    pe_lhs.var = inst.in[0];
    pe_lhs.real = &o->left;
    pe_rhs.error = 0;
    pe_rhs.var = inst.in[1];
    pe_rhs.real = &o->right;
    property_bound pb_lhs, pb_rhs, pb_res;
    pb_lhs.var = inst.in[0];
    pb_rhs.var = inst.in[1];
    pb_res.var = inst.out[0];
    node *nb_lhs, *nb_rhs, *nb_res, *ne_lhs, *ne_rhs;
    if (!(ne_lhs = generate_basic_proof_error(hyp, pe_lhs))) return NULL;
    if (!(ne_rhs = generate_basic_proof_error(hyp, pe_rhs))) return NULL;
    if (!(nb_res = generate_basic_proof_bound(hyp, pb_res))) return NULL;
    assert(pe_lhs.error == 0 && pe_rhs.error == 0);
    if (inst.fun->name->name == "add32") {
      res.err = pe_lhs.err + pe_rhs.err + from_exponent(ulp_exponent(pb_res.bnd), GMP_RNDN);
      return new node_plouf(hyp, res);
    }
    if (inst.fun->name->name == "mul32") {
      if (!(nb_lhs = generate_basic_proof_bound(hyp, pb_lhs))) return NULL;
      if (!(nb_rhs = generate_basic_proof_bound(hyp, pb_rhs))) return NULL;
      res.err = pe_lhs.err * to_real(pb_rhs.bnd) + pe_rhs.err * to_real(pb_lhs.bnd)
              + pe_lhs.err * pe_rhs.err + from_exponent(ulp_exponent(pb_res.bnd), GMP_RNDN);
      return new node_plouf(hyp, res);
    }
  }
  assert(false);
  return NULL;
}

node *do_generate_basic_proof::operator()(property_bound const &res) const {
  property_bound res2 = res;
  return generate_basic_proof_bound(hyp, res2);
}

node *do_generate_basic_proof::operator()(property_error const &res) const {
  property_error res2 = res;
  return generate_basic_proof_error(hyp, res2);
}

node *generate_basic_proof(property_vect const &hyp, property const &res) {
  return boost::apply_visitor(do_generate_basic_proof(hyp), res);
}
