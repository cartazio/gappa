#include "numbers/interval_utility.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/dichotomy.hpp"

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

struct dichotomy_failure {
  property_vect hyp;
  property res;
  interval bnd;
  dichotomy_failure(property_vect const &h, property const &r, interval const &b): hyp(h), res(r), bnd(b) {}
};

void dichotomize(property_vect &hyp, property &res, node_vect &nodes) {
  property const &h = hyp[0];
  interval bnd;
  {
    graph_layer layer(hyp);
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
  hyp.replace_front(property(h.real, ii.first));
  property res1 = res;
  dichotomize(hyp, res1, nodes);
  hyp.replace_front(property(h.real, ii.second));
  property res2 = res;
  dichotomize(hyp, res2, nodes);
  res.bnd = hull(res1.bnd, res2.bnd);
}

node *dichotomy_scheme::generate_proof(property_vect const &hyp, property &res) const {
  property varp(real);
  node *varn = handle_proof(hyp, varp);
  if (!varn) return NULL;
  try {
    property res2 = res;
    property_vect hyp2 = hyp;
    hyp2.push_front(varp);
    node_vect nodes;
    dichotomize(hyp2, res2, nodes);
    return new node_dichotomy(hyp, res2, nodes);
  } catch (dichotomy_failure e) { // BLI
    property const &h = e.hyp[0];
    ast_ident const *v = h.real->get_variable();
    assert(v);
    std::cerr << "failure: when " << v->name << " is " << h.bnd << ", ";
    property const &p = e.res;
    if (ast_ident const *v = p.real->get_variable())
      std::cerr << v->name;
    else
      std::cerr << "...";
    if (is_defined(e.bnd))
      std::cerr << " is in " << e.bnd << " potentially outside of " << p.bnd << '\n';
    else
      std::cerr << " is nowhere (?!)\n";
    return NULL;
  }
}

struct dichotomy_factory: scheme_factory {
  ast_real const *r1, *r2;
  dichotomy_factory(ast_real const *q1, ast_real const *q2): r1(q1), r2(q2) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *dichotomy_factory::operator()(ast_real const *r) const {
  if (r != r1) return NULL;
  return new dichotomy_scheme(r2);
}

void register_user_dichotomy(ast_real const *r1, ast_real const *r2) {
  scheme_register dummy(new dichotomy_factory(r1, r2));
}
