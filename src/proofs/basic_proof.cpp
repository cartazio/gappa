#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

#include <algorithm>
#include <iostream>
#include <map>
#include <boost/scoped_array.hpp>

/*
Trivialities are emitted when the result of a basic proof directly
matches one of the hypotheses. They all are the same node, and it does
not convey any interesting information. Consequently the result is
carried through the reference parameter. All the trivialities should be
destroyed by modus or assignation.
*/

node *triviality = (node *)1;

node_theorem::node_theorem(int nb, property const *h, property const &p, std::string n): node(THEOREM), name(n) {
  res = p;
  for(int i = 0; i < nb; ++i) hyp.push_back(h[i]);
}

node_modus::node_modus(node *n, property const &p): node(MODUS) {
  res = p;
  if (n == triviality) {
    /*
    if (error_bound const *e = boost::get< error_bound const >(p.real)) {
      assert(e->var->real == e->real);
    } else {
      variable const *v = res.real->get_variable();
      assert(v);
      instruction *inst = v->inst;
      assert(inst && !inst->fun);
      property h = res;
      h.real = inst->in[0]->real;
      hyp.push_back(h);
    }
    */
    return;
  }
  insert_pred(n);
  hyp = n->hyp;
}

node_modus::node_modus(property const &p, node *n, node_vect const &nodes): node(MODUS) {
  res = p;
  insert_pred(n);
  typedef std::map< ast_real const *, interval > property_map;
  property_map pmap, rmap;
  for(node_vect::const_iterator i = nodes.begin(), i_end = nodes.end(); i != i_end; ++i) {
    node *m = *i;
    if (m == triviality) continue;
    insert_pred(m);
    {
      property const &p = m->res;
      property_map::iterator pki = rmap.find(p.real);
      if (pki != rmap.end())
        pki->second = intersect(pki->second, p.bnd);
      else
        rmap.insert(std::make_pair(p.real, p.bnd));
    }
    for(property_vect::const_iterator j = m->hyp.begin(), j_end = m->hyp.end(); j != j_end; ++j) {
      property const &p = *j;
      property_map::iterator pki = pmap.find(p.real);
      if (pki != pmap.end())
        pki->second = hull(pki->second, p.bnd);
      else
        pmap.insert(std::make_pair(p.real, p.bnd));
    }
  }
  for(property_vect::const_iterator j = n->hyp.begin(), j_end = n->hyp.end(); j != j_end; ++j) {
    property const &p = *j;
    property_map::iterator pki = rmap.find(p.real); // is the hypothesis a result?
    if (pki != rmap.end() && pki->second <= p.bnd) continue;
    pki = pmap.find(p.real);
    if (pki != pmap.end())
      pki->second = hull(pki->second, p.bnd);
    else
      pmap.insert(std::make_pair(p.real, p.bnd));
  }
  for(property_map::const_iterator pki = pmap.begin(), pki_end = pmap.end(); pki != pki_end; ++pki) {
    property p(pki->first, pki->second);
    hyp.push_back(p);
  }
}

// no node should be generated and res should only be modified upon success
node *generate_triviality(property_vect const &hyp, property &res, bool &optimal) {
  node *n = graph->find_in_cache(hyp, res);
  optimal = n;
  if (!optimal) {
    int i = hyp.find_compatible_property(res);
    if (i >= 0) {
      res = hyp[i];
      return triviality;
    }
    n = graph->find_compatible_node(hyp, res);
  }
  if (n) res = n->res;
  return n;
}

// ABSOLUTE_ERROR_FROM_REAL
struct absolute_error_from_real_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *absolute_error_from_real_scheme::generate_proof(property_vect const &hyp, property &res) const {
  real_op const *o = boost::get< real_op const >(res.real);
  assert(o && o->type == BOP_SUB);
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  assert(rr && o->ops[0] == rr->rounded);
  property res2(rr->rounded);
  node *n = handle_proof(hyp, res2);
  if (!n) return NULL;
  std::string name;
  interval bnd = rr->rounding->error_from_real(res2.bnd, name);
  if (!(bnd <= res.bnd)) return NULL;
  res.bnd = bnd;
  node_vect nodes;
  nodes.push_back(n);
  return new node_modus(res, new node_theorem(1, &res2, res, name), nodes);
}

ast_real_vect absolute_error_from_real_scheme::needed_reals(ast_real const *real) const {
  real_op const *o = boost::get< real_op const >(real);
  assert(o && o->type == BOP_SUB);
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  assert(rr && o->ops[0] == rr->rounded);
  return ast_real_vect(1, rr->rounded);
}

proof_scheme *absolute_error_from_real_scheme::factory(ast_real const *r) {
  real_op const *o = boost::get< real_op const >(r);
  if (!o) return NULL;
  if (o->type != BOP_SUB) return NULL;
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  if (!rr || o->ops[0] != rr->rounded) return NULL;
  return new absolute_error_from_real_scheme;
}

scheme_register absolute_error_from_real_scheme_register(&absolute_error_from_real_scheme::factory);

// ABSOLUTE_ERROR_FROM_ROUNDED
struct absolute_error_from_rounded_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *absolute_error_from_rounded_scheme::generate_proof(property_vect const &hyp, property &res) const {
  real_op const *o = boost::get< real_op const >(res.real);
  assert(o && o->type == BOP_SUB);
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  assert(rr && o->ops[0] == rr->rounded);
  property res2(o->ops[1]);
  node *n = handle_proof(hyp, res2);
  if (!n) return NULL;
  std::string name;
  interval bnd = rr->rounding->error_from_rounded(res2.bnd, name);
  if (!(bnd <= res.bnd)) return NULL;
  res.bnd = bnd;
  node_vect nodes;
  nodes.push_back(n);
  return new node_modus(res, new node_theorem(1, &res2, res, name), nodes);
}

ast_real_vect absolute_error_from_rounded_scheme::needed_reals(ast_real const *real) const {
  real_op const *o = boost::get< real_op const >(real);
  assert(o && o->type == BOP_SUB);
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  assert(rr && o->ops[0] == rr->rounded);
  return ast_real_vect(1, o->ops[1]);
}

proof_scheme *absolute_error_from_rounded_scheme::factory(ast_real const *r) {
  real_op const *o = boost::get< real_op const >(r);
  if (!o) return NULL;
  if (o->type != BOP_SUB) return NULL;
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  if (!rr || o->ops[0] != rr->rounded) return NULL;
  return new absolute_error_from_rounded_scheme;
}

scheme_register absolute_error_from_rounded_scheme_register(&absolute_error_from_rounded_scheme::factory);

// ROUNDING_BOUND
struct rounding_bound_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *rounding_bound_scheme::generate_proof(property_vect const &hyp, property &res) const {
  rounded_real const *r = boost::get< rounded_real const >(res.real);
  assert(r);
  property res2(r->rounded);
  node *n = handle_proof(hyp, res2);
  if (!n) return NULL;
  std::string name;
  interval bnd = r->rounding->bound(res2.bnd, name);
  if (!(bnd <= res.bnd)) return NULL;
  res.bnd = bnd;
  node_vect nodes;
  nodes.push_back(n);
  return new node_modus(res, new node_theorem(1, &res2, res, name), nodes);
}

ast_real_vect rounding_bound_scheme::needed_reals(ast_real const *real) const {
  rounded_real const *r = boost::get< rounded_real const >(real);
  assert(r);
  return ast_real_vect(1, r->rounded);
}

proof_scheme *rounding_bound_scheme::factory(ast_real const *r) {
  if (!boost::get< rounded_real const >(r)) return NULL;
  return new rounding_bound_scheme;
}

scheme_register rounding_bound_scheme_register(&rounding_bound_scheme::factory);

// COMPUTATION
struct computation_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *computation_scheme::generate_proof(property_vect const &hyp, property &res) const {
  real_op const *r = boost::get< real_op const >(res.real);
  assert(r);
  node_vect nodes;
  node *n = NULL;
  switch (r->ops.size()) {
  case 1: {
    assert(r->type == UOP_MINUS);
    property res1(r->ops[0]);
    if (is_defined(res.bnd)) res1.bnd = -res.bnd;
    node *n1 = handle_proof(hyp, res1);
    if (!n1) return NULL;
    res.bnd = -res1.bnd;
    nodes.push_back(n1);
    n = new node_theorem(1, &res1, res, "neg");
    break; }
  case 2: {
    bool same_ops = r->ops[0] == r->ops[1];
    if (same_ops && r->type == BOP_SUB) {
      if (!contains_zero(res.bnd)) return NULL;
      res.bnd = zero();
      return new node_theorem(0, NULL, res, "sub_refl");
    }
    property res1(r->ops[0]);
    bool do_square = same_ops && r->type == BOP_MUL;
    if (do_square) res1.bnd = square_rev(res.bnd);
    node *n1 = handle_proof(hyp, res1);
    if (!n1) return NULL;
    interval const &i1 = res1.bnd;
    if (do_square) {
      interval i = square(i1);
      if (!(i <= res.bnd)) return NULL;
      res.bnd = i;
      nodes.push_back(n1);
      n = new node_theorem(1, &res1, res, "square");
      break;
    }
    property res2(r->ops[1]);
    switch (r->type) {
    case BOP_ADD: res2.bnd = add_rev(i1, res.bnd); break;
    case BOP_SUB: res2.bnd = sub_rev(i1, res.bnd); break;
    default: ;
    }
    node *n2 = handle_proof(hyp, res2);
    if (!n2) return NULL;
    interval const &i2 = res2.bnd;
    char const *s = NULL;
    interval i;
    switch (r->type) {
    case BOP_ADD: i = i1 + i2; s = "add"; break;
    case BOP_SUB: i = i1 - i2; s = "sub"; break;
    case BOP_MUL: i = i1 * i2; s = "mul"; break;
    case BOP_DIV:
      if (contains_zero(i2)) return NULL;
      i = i1 / i2;
      s = "div";
      break;
    default:
      assert(false);
      return NULL;
    }
    if (!(i <= res.bnd)) return NULL;
    res.bnd = i;
    nodes.push_back(n1);
    nodes.push_back(n2);
    property hyps[2] = { res1, res2 };
    n = new node_theorem(2, hyps, res, s);
    break; }
  default:
    assert(false);
  }
  return new node_modus(res, n, nodes);
}

ast_real_vect computation_scheme::needed_reals(ast_real const *real) const {
  real_op const *r = boost::get< real_op const >(real);
  assert(r);
  if (r->type == BOP_SUB && r->ops[0] == r->ops[1])
    return ast_real_vect(); // special case, x-x is always 0
  return r->ops;
}

proof_scheme *computation_scheme::factory(ast_real const *r) {
  if (!boost::get< real_op const >(r)) return NULL;
  return new computation_scheme;
}

scheme_register computation_scheme_register(&computation_scheme::factory);

// NUMBER
struct number_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
  static proof_scheme *factory(ast_real const *);
};

interval create_interval(ast_interval const &, bool widen = true);

node *number_scheme::generate_proof(property_vect const &, property &res) const {
  ast_number const *const *r = boost::get< ast_number const *const >(res.real);
  assert(r);
  ast_interval _i = { *r, *r };
  interval i = create_interval(_i);
  if (!(i <= res.bnd)) return NULL;
  res.bnd = i;
  return new node_theorem(0, NULL, res, "constant");
}

proof_scheme *number_scheme::factory(ast_real const *r) {
  if (!boost::get< ast_number const *const >(r)) return NULL;
  return new number_scheme;
}

scheme_register number_scheme_register(&number_scheme::factory);

// REWRITE
node *rewrite_scheme::generate_proof(property_vect const &hyp, property &res) const {
  property res2(real, res.bnd);
  node *n = handle_proof(hyp, res2);
  if (!n) return NULL;
  res.bnd = res2.bnd;
  node_vect nodes;
  nodes.push_back(n);
  return new node_modus(res, new node_theorem(1, &res2, res, name), nodes);
}

struct rewrite_factory: scheme_factory {
  ast_real const *r1, *r2;
  std::string name;
  rewrite_factory(ast_real const *q1, ast_real const *q2): r1(q1), r2(q2) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *rewrite_factory::operator()(ast_real const *r) const {
  if (r != r1) return NULL;
  return new rewrite_scheme(r2, "user_defined");
}

void register_user_rewrite(ast_real const *r1, ast_real const *r2) {
  scheme_register dummy(new rewrite_factory(r1, r2));
}
