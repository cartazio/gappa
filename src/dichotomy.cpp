#include <iostream>
#include "basic_proof.hpp"
#include "proof_graph.hpp"
#include "program.hpp"
#include "ast.hpp"
#include "interval_ext.hpp"
#include "function.hpp"

struct node_plouf: node {
  node_plouf(property_vect const &h, property const &p): node(OTHER) {
    res = p;
    hyp = h;
  }
};

namespace dichotomy {
} // namespace dichotomy

namespace basic_proof {
interval compute_bound(property_vect const &hyp, variable *v);
} // namespace basic_proof

namespace {

std::vector< variable * > multiple_definition(variable *v) {
  std::vector< variable * > res;
  res.push_back(ast_ident::find("x")->var);
  return res;
}

void dichotomize(property_vect &hyp, property_bound &res, int idx) {
  property_bound *p = boost::get< property_bound >(&hyp[idx]);
  assert(p);
  interval bnd = basic_proof::compute_bound(hyp, res.var);
  if (is_defined(bnd) && bnd <= res.bnd) {
    std::cout << "  " << p->bnd << " -> " << bnd << std::endl;
    res.bnd = bnd;
    return;
  }
  assert(!is_singleton(p->bnd));
  std::pair< interval, interval > ii = split(p->bnd);
  p->bnd = ii.first;
  property_bound res1 = res;
  dichotomize(hyp, res1, idx);
  p->bnd = ii.second;
  property_bound res2 = res;
  dichotomize(hyp, res2, idx);
  res.bnd = hull(res1.bnd, res2.bnd);
}

} // anonymous namespace

node *generate_proof(property_vect const &hyp, property const &res) {
  if (node *n = generate_basic_proof(hyp, res)) return n;
  property_bound const *p = boost::get< property_bound const >(&res);
  if (!p || !is_defined(p->bnd)) return NULL;
  std::vector< variable * > vars = multiple_definition(p->var);
  int i;
  property_bound bnd;
  bnd.var = vars[0];
  i = hyp.find_compatible_property(bnd);
  assert(i >= 0);
  bnd.var = p->var;
  bnd.bnd = p->bnd;
  property_vect hyp2 = hyp;
  dichotomize(hyp2, bnd, i);
  return new node_plouf(hyp, bnd);
}
