#include <iostream>
#include "basic_proof.hpp"
#include "proof_graph.hpp"
#include "program.hpp"
#include "ast.hpp"
#include "numbers/interval_ext.hpp"
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
node *generate_error(property_vect const &hyp, property &res);
} // namespace basic_proof

namespace {

std::vector< variable * > multiple_definition(variable *) {
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

interval compute_error(property_vect const &hyp, property const &res) { // TODO
  property tmp = res;
  tmp.bnd = interval();
  graph_layer layer;
  node *n = basic_proof::generate_error(hyp, tmp);
  if (!n) return interval();
  return tmp.bnd;
}

void dichotomize(property_vect &hyp, property &res, int idx) {
  property &h = hyp[idx];
  assert(h.type == PROP_BND);
  interval bnd = res.type == PROP_BND ? basic_proof::compute_bound(hyp, res.var) : compute_error(hyp, res);
  if (is_defined(bnd) && bnd <= res.bnd) {
    //std::cout << "  " << h.bnd << " -> " << bnd << std::endl;
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
  {
    graph_layer layer;
    if (node *n = generate_basic_proof(hyp, res)) { layer.flatten(); return n; }
  }
  if (!is_defined(res.bnd)) return NULL;
  std::vector< variable * > vars = multiple_definition(res.var);
  int i;
  property bnd(PROP_BND); // TODO
  bnd.var = vars[0];
  i = hyp.find_compatible_property(bnd);
  assert(i >= 0);
  property res2 = res;
  property_vect hyp2 = hyp;
  try {
    dichotomize(hyp2, res2, i);
  } catch (dichotomy_failure e) {
    property &h = e.hyp[i];
    std::cerr << "dichotomy failure: when " << h.var->name->name << " is " << h.bnd << ", ";
    property &p = e.res;
    std::string const &name = p.var->name->name;
    if (p.type == PROP_BND)
      std::cerr << name;
    else if (p.type == PROP_ABS || p.type == PROP_REL)
      std::cerr << (p.type == PROP_ABS ? "ABS(" : "REL(") << name << ", ...)";
    else assert(false);
    std::cerr << " is in " << e.bnd << " potentially outside of " << p.bnd << std::endl;
    return NULL;
  }
  return new node_plouf(hyp, res2);
}
