#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

struct rewrite_node: public theorem_node {
  ast_real_vect subs;
  rewrite_node(int nb, property const h[], property const &p, std::string const &n, ast_real_vect const &s)
    : theorem_node(nb, h, p, n), subs(s) {}
  virtual ast_real_vect sub_expressions() const { return subs; }
};

static bool absolute_error_decomposition(ast_real const *real, ast_real const **f, rounded_real const **r) {
  real_op const *o = boost::get< real_op const >(real);
  if (!o || o->type != BOP_SUB) return false;
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[0]);
  if (!rr || o->ops[1] != rr->rounded) return false;
  if (f) *f = o->ops[0];
  if (r) *r = rr;
  return true;
}

static bool relative_error_decomposition(ast_real const *real, ast_real const **f, rounded_real const **r) {
  real_op const *o1 = boost::get< real_op const >(real);
  if (!o1 || o1->type != BOP_DIV) return false;
  real_op const *o2 = boost::get< real_op const >(o1->ops[0]);
  if (!o2 || o2->type != BOP_SUB || o1->ops[1] != o2->ops[1]) return false;
  rounded_real const *rr = boost::get< rounded_real const >(o2->ops[0]);
  if (!rr || o2->ops[1] != rr->rounded) return false;
  if (f) *f = o2->ops[0];
  if (r) *r = rr;
  return true;
}

// ABSOLUTE_ERROR_FROM_REAL
struct absolute_error_from_real_scheme: proof_scheme {
  absolute_error_from_real_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
  static proof_scheme *factory(ast_real const *);
};

node *absolute_error_from_real_scheme::generate_proof() const {
  rounded_real const *rr;
  bool b = absolute_error_decomposition(real, NULL, &rr);
  assert(b);
  node *n = find_proof(rr->rounded);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, rr->rounding->absolute_error_from_real(res1.bnd, name));
  if (!is_defined(res.bnd)) return NULL;
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
}

ast_real_vect absolute_error_from_real_scheme::needed_reals() const {
  rounded_real const *rr;
  bool b = absolute_error_decomposition(real, NULL, &rr);
  assert(b);
  return ast_real_vect(1, rr->rounded);
}

proof_scheme *absolute_error_from_real_scheme::factory(ast_real const *real) {
  if (!absolute_error_decomposition(real, NULL, NULL)) return NULL;
  return new absolute_error_from_real_scheme(real);
}

static scheme_register absolute_error_from_real_scheme_register(&absolute_error_from_real_scheme::factory);

// ABSOLUTE_ERROR_FROM_ROUNDED
struct absolute_error_from_rounded_scheme: proof_scheme {
  absolute_error_from_rounded_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
  static proof_scheme *factory(ast_real const *);
};

node *absolute_error_from_rounded_scheme::generate_proof() const {
  ast_real const *r; rounded_real const *rr;
  bool b = absolute_error_decomposition(real, &r, &rr);
  assert(b);
  node *n = find_proof(r);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, rr->rounding->absolute_error_from_rounded(res1.bnd, name));
  if (!is_defined(res.bnd)) return NULL;
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
}

ast_real_vect absolute_error_from_rounded_scheme::needed_reals() const {
  ast_real const *r;
  bool b = absolute_error_decomposition(real, &r, NULL);
  assert(b);
  return ast_real_vect(1, r);
}

proof_scheme *absolute_error_from_rounded_scheme::factory(ast_real const *real) {
  if (!absolute_error_decomposition(real, NULL, NULL)) return NULL;
  return new absolute_error_from_rounded_scheme(real);
}

static scheme_register absolute_error_from_rounded_scheme_register(&absolute_error_from_rounded_scheme::factory);

// RELATIVE_ERROR_FROM_REAL
struct relative_error_from_real_scheme: proof_scheme {
  relative_error_from_real_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
  static proof_scheme *factory(ast_real const *);
};

node *relative_error_from_real_scheme::generate_proof() const {
  rounded_real const *rr;
  bool b = relative_error_decomposition(real, NULL, &rr);
  assert(b);
  node *n = find_proof(rr->rounded);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, rr->rounding->relative_error_from_real(res1.bnd, name));
  if (!is_defined(res.bnd)) return NULL;
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
}

ast_real_vect relative_error_from_real_scheme::needed_reals() const {
  rounded_real const *rr;
  bool b = relative_error_decomposition(real, NULL, &rr);
  assert(b);
  return ast_real_vect(1, rr->rounded);
}

proof_scheme *relative_error_from_real_scheme::factory(ast_real const *real) {
  if (!relative_error_decomposition(real, NULL, NULL)) return NULL;
  return new relative_error_from_real_scheme(real);
}

static scheme_register relative_error_from_real_scheme_register(&relative_error_from_real_scheme::factory);

// RELATIVE_ERROR_FROM_ROUNDED
struct relative_error_from_rounded_scheme: proof_scheme {
  relative_error_from_rounded_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
  static proof_scheme *factory(ast_real const *);
};

node *relative_error_from_rounded_scheme::generate_proof() const {
  ast_real const *r; rounded_real const *rr;
  bool b = relative_error_decomposition(real, &r, &rr);
  assert(b);
  node *n = find_proof(r);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, rr->rounding->relative_error_from_rounded(res1.bnd, name));
  if (!is_defined(res.bnd)) return NULL;
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
}

ast_real_vect relative_error_from_rounded_scheme::needed_reals() const {
  ast_real const *r;
  bool b = relative_error_decomposition(real, &r, NULL);
  assert(b);
  return ast_real_vect(1, r);
}

proof_scheme *relative_error_from_rounded_scheme::factory(ast_real const *real) {
  if (!relative_error_decomposition(real, NULL, NULL)) return NULL;
  return new relative_error_from_rounded_scheme(real);
}

static scheme_register relative_error_from_rounded_scheme_register(&relative_error_from_rounded_scheme::factory);

// ROUNDING_BOUND
struct rounding_bound_scheme: proof_scheme {
  rounding_bound_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
  static proof_scheme *factory(ast_real const *);
};

node *rounding_bound_scheme::generate_proof() const {
  rounded_real const *r = boost::get< rounded_real const >(real);
  assert(r);
  node *n = find_proof(r->rounded);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, r->rounding->round(res1.bnd, name));
  if (!is_defined(res.bnd)) return NULL;
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
}

ast_real_vect rounding_bound_scheme::needed_reals() const {
  rounded_real const *r = boost::get< rounded_real const >(real);
  assert(r);
  return ast_real_vect(1, r->rounded);
}

proof_scheme *rounding_bound_scheme::factory(ast_real const *real) {
  if (!boost::get< rounded_real const >(real)) return NULL;
  return new rounding_bound_scheme(real);
}

static scheme_register rounding_bound_scheme_register(&rounding_bound_scheme::factory);

// ENFORCE_BOUND
struct enforce_bound_scheme: proof_scheme {
  enforce_bound_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
  static proof_scheme *factory(ast_real const *);
};

node *enforce_bound_scheme::generate_proof() const {
  rounded_real const *r = boost::get< rounded_real const >(real);
  assert(r);
  node *n = find_proof(real);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, r->rounding->enforce(res1.bnd, name));
  if (!is_defined(res.bnd)) return NULL;
  return new modus_node(1, &n, new theorem_node(1, &res1, res, name));
}

ast_real_vect enforce_bound_scheme::needed_reals() const {
  rounded_real const *r = boost::get< rounded_real const >(real);
  assert(r);
  return ast_real_vect(1, real);
}

proof_scheme *enforce_bound_scheme::factory(ast_real const *real) {
  if (!boost::get< rounded_real const >(real)) return NULL;
  return new enforce_bound_scheme(real);
}

static scheme_register enforce_bound_scheme_register(&enforce_bound_scheme::factory);

// COMPUTATION
struct computation_scheme: proof_scheme {
  computation_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const;
  static proof_scheme *factory(ast_real const *);
};

node *computation_scheme::generate_proof() const {
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
      return new rewrite_node(0, NULL, property(real, zero()), "sub_refl", ast_real_vect(1, r->ops[0]));
    std::string s;
    node *n1 = find_proof(r->ops[0]);
    if (!n1) return NULL;
    property const &res1 = n1->get_result();
    interval const &i1 = res1.bnd;
    if (same_ops && r->type == BOP_MUL) {
      nodes.push_back(n1);
      s = "square_";
      s += 'o' + sign(i1);
      n = new theorem_node(1, &res1, property(real, square(i1)), s);
      break;
    }
    node *n2 = find_proof(r->ops[1]);
    if (!n2) return NULL;
    property const &res2 = n2->get_result();
    interval const &i2 = res2.bnd;
    property res(real);
    interval &i = res.bnd;
    switch (r->type) {
    case BOP_ADD: i = i1 + i2; s = "add"; break;
    case BOP_SUB: i = i1 - i2; s = "sub"; break;
    case BOP_MUL:
      i = i1 * i2;
      s = "mul_";
      s += 'o' + sign(i1);
      s += 'o' + sign(i2);
      break;
    case BOP_DIV:
      if (contains_zero(i2)) return NULL;
      i = i1 / i2;
      s = "div";
      s += 'o' + sign(i1);
      s += 'o' + sign(i2);
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

ast_real_vect computation_scheme::needed_reals() const {
  real_op const *r = boost::get< real_op const >(real);
  assert(r);
  if (r->type == BOP_SUB && r->ops[0] == r->ops[1])
    return ast_real_vect(); // special case, x-x is always 0
  return r->ops;
}

proof_scheme *computation_scheme::factory(ast_real const *real) {
  if (!boost::get< real_op const >(real)) return NULL;
  return new computation_scheme(real);
}

static scheme_register computation_scheme_register(&computation_scheme::factory);

// NUMBER
struct number_scheme: proof_scheme {
  number_scheme(ast_real const *r): proof_scheme(r) {}
  virtual node *generate_proof() const;
  virtual ast_real_vect needed_reals() const { return ast_real_vect(); }
  static proof_scheme *factory(ast_real const *);
};

interval create_interval(ast_interval const &, bool widen = true);

node *number_scheme::generate_proof() const {
  ast_number const *const *r = boost::get< ast_number const *const >(real);
  assert(r);
  ast_interval _i = { *r, *r };
  char const *s;
  if ((**r).base == 0 || (**r).exponent == 0) s = "constant1";
  else if ((**r).base == 2) s = "constant2";
  else s = "constant10";
  return new theorem_node(0, NULL, property(real, create_interval(_i)), s);
}

proof_scheme *number_scheme::factory(ast_real const *real) {
  if (!boost::get< ast_number const *const >(real)) return NULL;
  return new number_scheme(real);
}

static scheme_register number_scheme_register(&number_scheme::factory);

// REWRITE
node *rewrite_scheme::generate_proof() const {
  node *n = find_proof(rewritten);
  if (!n) return NULL;
  property const &res = n->get_result();
  return new modus_node(1, &n, new rewrite_node(1, &res, property(real, res.bnd), name, subs));
}

struct rewrite_factory: scheme_factory {
  ast_real const *src, *dst;
  std::string name;
  rewrite_factory(ast_real const *q1, ast_real const *q2): src(q1), dst(q2) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *rewrite_factory::operator()(ast_real const *r) const {
  if (r != src) return NULL;
  return new rewrite_scheme(src, dst, "user_defined", ast_real_vect());
}

void register_user_rewrite(ast_real const *r1, ast_real const *r2) {
  scheme_register dummy(new rewrite_factory(r1, r2));
}
