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

struct dichotomy_failure {
  property_vect hyp;
  property res;
  interval bnd;
  dichotomy_failure(property_vect const &h, property const &r, interval const &b): hyp(h), res(r), bnd(b) {}
};

void dichotomize(property_vect &hyp, property &res, int idx) {
  property &h = hyp[idx];
  assert(res.type == PROP_BND && h.type == PROP_BND);
  interval bnd = basic_proof::compute_bound(hyp, res.var);
  if (is_defined(bnd) && bnd <= res.bnd) {
    //std::cout << "  " << p->bnd << " -> " << bnd << std::endl;
    res.bnd = bnd;
    return;
  }
  if (is_singleton(h.bnd)) throw dichotomy_failure(hyp, res, bnd);
  std::pair< interval, interval > ii = split(h.bnd);
  h.bnd = ii.first;
  property res1 = res;
  dichotomize(hyp, res1, idx);
  h.bnd = ii.second;
  property res2 = res;
  dichotomize(hyp, res2, idx);
  res.bnd = hull(res1.bnd, res2.bnd);
}

} // anonymous namespace

node *generate_proof(property_vect const &hyp, property const &res) {
  if (node *n = generate_basic_proof(hyp, res)) return n;
  if (res.type != PROP_BND || !is_defined(res.bnd)) return NULL;
  std::vector< variable * > vars = multiple_definition(res.var);
  int i;
  property bnd(PROP_BND);
  bnd.var = vars[0];
  i = hyp.find_compatible_property(bnd);
  assert(i >= 0);
  bnd.var = res.var;
  bnd.bnd = res.bnd;
  property_vect hyp2 = hyp;
  try {
    dichotomize(hyp2, bnd, i);
  } catch (dichotomy_failure e) {
    std::cerr
      << "dichotomy failure: when "
      << e.hyp[i].var->name->name << " is " << e.hyp[i].bnd << ", "
      << e.res.var->name->name << " is in " << e.bnd
      << " potentially outside of " << e.res.bnd << std::endl;
    return NULL;
  }
  return new node_plouf(hyp, bnd);
}
