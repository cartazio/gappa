#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

/*
Trivialities are emitted when the result of a basic proof directly
matches one of the hypotheses. They all are the same node, and it does
not convey any interesting information. Consequently the result is
carried through the reference parameter. All the trivialities should be
destroyed by modus or assignation.
*/

// ABSOLUTE_ERROR_FROM_REAL
struct absolute_error_from_real_scheme: proof_scheme {
  virtual node *generate_proof(ast_real const *) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *absolute_error_from_real_scheme::generate_proof(ast_real const *real) const {
  real_op const *o = boost::get< real_op const >(real);
  assert(o && o->type == BOP_SUB);
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  assert(rr && o->ops[0] == rr->rounded);
  node *n = find_proof(rr->rounded);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, rr->rounding->error_from_real(res1.bnd, name));
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
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
  virtual node *generate_proof(ast_real const *) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *absolute_error_from_rounded_scheme::generate_proof(ast_real const *real) const {
  real_op const *o = boost::get< real_op const >(real);
  assert(o && o->type == BOP_SUB);
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  assert(rr && o->ops[0] == rr->rounded);
  node *n = find_proof(o->ops[1]);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, rr->rounding->error_from_rounded(res1.bnd, name));
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
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
  virtual node *generate_proof(ast_real const *) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *rounding_bound_scheme::generate_proof(ast_real const *real) const {
  rounded_real const *r = boost::get< rounded_real const >(real);
  assert(r);
  node *n = find_proof(r->rounded);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, r->rounding->bound(res1.bnd, name));
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
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
  virtual node *generate_proof(ast_real const *) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *computation_scheme::generate_proof(ast_real const *real) const {
  real_op const *r = boost::get< real_op const >(real);
  assert(r);
  node_vect nodes;
  node *n = NULL;
  switch (r->ops.size()) {
  case 1: {
    assert(r->type == UOP_MINUS);
    node *n1 = find_proof(r->ops[0]);
    if (!n1) return NULL;
    property const &res = n1->get_result();
    nodes.push_back(n1);
    n = new theorem_node(1, &res, property(real, -res.bnd), "neg");
    break; }
  case 2: {
    bool same_ops = r->ops[0] == r->ops[1];
    if (same_ops && r->type == BOP_SUB)
      return new theorem_node(0, NULL, property(real, zero()), "sub_refl");
    node *n1 = find_proof(r->ops[0]);
    if (!n1) return NULL;
    property const &res1 = n1->get_result();
    interval const &i1 = res1.bnd;
    if (same_ops && r->type == BOP_MUL) {
      nodes.push_back(n1);
      n = new theorem_node(1, &res1, property(real, square(i1)), "square");
      break;
    }
    node *n2 = find_proof(r->ops[1]);
    if (!n2) return NULL;
    property const &res2 = n2->get_result();
    interval const &i2 = res2.bnd;
    char const *s = NULL;
    property res(real);
    interval &i = res.bnd;
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
    nodes.push_back(n1);
    nodes.push_back(n2);
    property hyps[2] = { res1, res2 };
    n = new theorem_node(2, hyps, res, s);
    break; }
  default:
    assert(false);
  }
  return new modus_node(nodes.size(), &nodes.front(), n);
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
  virtual node *generate_proof(ast_real const *) const;
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
  static proof_scheme *factory(ast_real const *);
};

interval create_interval(ast_interval const &, bool widen = true);

node *number_scheme::generate_proof(ast_real const *real) const {
  ast_number const *const *r = boost::get< ast_number const *const >(real);
  assert(r);
  ast_interval _i = { *r, *r };
  return new theorem_node(0, NULL, property(real, create_interval(_i)), "constant");
}

proof_scheme *number_scheme::factory(ast_real const *r) {
  if (!boost::get< ast_number const *const >(r)) return NULL;
  return new number_scheme;
}

scheme_register number_scheme_register(&number_scheme::factory);

// REWRITE
node *rewrite_scheme::generate_proof(ast_real const *r) const {
  node *n = find_proof(real);
  if (!n) return NULL;
  property const &res = n->get_result();
  return new modus_node(1, &n, new theorem_node(1, &res, property(r, res.bnd), name));
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
