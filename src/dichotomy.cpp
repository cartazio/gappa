#include "ast.hpp"
#include "basic_proof.hpp"
#include "function.hpp"
#include "numbers/interval_utility.hpp"
#include "program.hpp"
#include "proof_graph.hpp"

#include <algorithm>
#include <boost/bind.hpp>
#include <iostream>

struct node_dichotomy: node {
  node_dichotomy(property_vect const &h, property const &p, node_vect const &n): node(UNION) {
    res = p;
    hyp = h;
    std::for_each(n.begin(), n.end(), boost::bind(&node_dichotomy::insert_pred, this, _1));
  }
};

namespace dichotomy {
} // namespace dichotomy

namespace basic_proof {
interval compute_bound(property_vect const &hyp, ast_real const *r);
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

void dichotomize(property_vect &hyp, property &res, int idx, node_vect &nodes) {
  property &h = hyp[idx];
  interval bnd;
  {
    graph_layer layer;
    property res0 = res;
    node *n = handle_proof(hyp, res0);
    if (n) {
      bnd = res0.bnd;
      if (bnd <= res.bnd) {
        nodes.push_back(n);
        layer.flatten();
        return;
      }
    }
  }
  if (is_singleton(h.bnd)) throw dichotomy_failure(hyp, res, bnd);
  std::pair< interval, interval > ii = split(h.bnd/*, TODO*/);
  h.bnd = ii.first;
  property res1 = res;
  dichotomize(hyp, res1, idx, nodes);
  h.bnd = ii.second;
  property res2 = res;
  dichotomize(hyp, res2, idx, nodes);
  res.bnd = hull(res1.bnd, res2.bnd);
}

} // anonymous namespace

node *generate_dichotomy_proof(property_vect const &hyp, property &res) {
  //std::vector< variable * > vars = multiple_definition(res.var); // BLI
  int i;
  property bnd(ast_ident::find("x")->var->real); // TODO
  i = hyp.find_compatible_property(bnd);
  assert(i >= 0);
  try {
    property res2 = res;
    property_vect hyp2 = hyp;
    node_vect nodes;
    dichotomize(hyp2, res2, i, nodes);
    return new node_dichotomy(hyp, res2, nodes);
  } catch (dichotomy_failure e) { // BLI
    property &h = e.hyp[i];
    variable const *v = h.real->get_variable();
    assert(v);
    std::cerr << "failure: when " << v->name->name << " is " << h.bnd << ", ";
    property &p = e.res;
    if (error_bound const *e = boost::get< error_bound const >(p.real))
      std::cerr << (e->type == ERROR_ABS ? "ABS(" : "REL(") << e->var->name->name << ", ...)";
    else if (variable const *v = p.real->get_variable())
      std::cerr << v->name->name;
    else
      std::cerr << "...";
    if (is_defined(e.bnd))
      std::cerr << " is in " << e.bnd << " potentially outside of " << p.bnd << '\n';
    else
      std::cerr << " is nowhere (?!)\n";
    return NULL;
  }
}
