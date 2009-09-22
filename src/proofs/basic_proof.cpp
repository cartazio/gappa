#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"
#include "proofs/updater.hpp"

static preal_vect one_needed(ast_real const *r) {
  return preal_vect(1, predicated_real(r, PRED_BND));
}

static bool is_changing_sign(ast_real const *r)
{
  real_op const *p = boost::get< real_op const >(r);
  return p && (p->type == UOP_ABS || p->type == UOP_NEG);
}

bool is_hidden(ast_real const *r)
{
  return boost::get< hidden_real const >(r);
}

// ABSOLUTE_ERROR
REGISTER_SCHEME_BEGIN(absolute_error);
  function_class const *function;
  absolute_error_scheme(ast_real const *r, function_class const *f)
    : proof_scheme(r), function(f) {}
REGISTER_SCHEME_END(absolute_error);

node *absolute_error_scheme::generate_proof() const {
  std::string name;
  property res(real, function->absolute_error(name));
  assert(is_defined(res.bnd()));
  return create_theorem(0, NULL, res, name);
}

preal_vect absolute_error_scheme::needed_reals() const {
  return preal_vect();
}

proof_scheme *absolute_error_scheme::factory(ast_real const *real) {
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS)) return NULL;
  return new absolute_error_scheme(real, f);
}

// ABSOLUTE_ERROR_FROM_EXACT_BND
REGISTER_SCHEME_BEGIN(absolute_error_from_exact_bnd);
  ast_real const *exact;
  function_class const *function;
  absolute_error_from_exact_bnd_scheme(ast_real const *r, ast_real const *e, function_class const *f)
    : proof_scheme(r), exact(e), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_exact_bnd);

node *absolute_error_from_exact_bnd_scheme::generate_proof() const {
  node *n = find_proof(exact);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->absolute_error_from_exact_bnd(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect absolute_error_from_exact_bnd_scheme::needed_reals() const {
  return one_needed(exact);
}

proof_scheme *absolute_error_from_exact_bnd_scheme::factory(ast_real const *real) {
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS_EXA_BND)) return NULL;
  return new absolute_error_from_exact_bnd_scheme(real, holders[0], f);
}

// ABSOLUTE_ERROR_FROM_EXACT_ABS
REGISTER_SCHEME_BEGIN(absolute_error_from_exact_abs);
  predicated_real exact;
  function_class const *function;
  absolute_error_from_exact_abs_scheme(ast_real const *r, predicated_real const &e, function_class const *f)
    : proof_scheme(r), exact(e), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_exact_abs);

node *absolute_error_from_exact_abs_scheme::generate_proof() const {
  node *n = find_proof(exact);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->absolute_error_from_exact_bnd(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect absolute_error_from_exact_abs_scheme::needed_reals() const {
  return preal_vect(1, exact);
}

proof_scheme *absolute_error_from_exact_abs_scheme::factory(ast_real const *real) {
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS_EXA_ABS)) return NULL;
  return new absolute_error_from_exact_abs_scheme(real, predicated_real(holders[0], PRED_ABS), f);
}

// ABSOLUTE_ERROR_FROM_APPROX_BND
REGISTER_SCHEME_BEGIN(absolute_error_from_approx_bnd);
  ast_real const *approx;
  function_class const *function;
  absolute_error_from_approx_bnd_scheme(ast_real const *r, ast_real const *a, function_class const *f)
    : proof_scheme(r), approx(a), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_approx_bnd);

node *absolute_error_from_approx_bnd_scheme::generate_proof() const {
  node *n = find_proof(approx);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->absolute_error_from_approx_bnd(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect absolute_error_from_approx_bnd_scheme::needed_reals() const {
  return one_needed(approx);
}

proof_scheme *absolute_error_from_approx_bnd_scheme::factory(ast_real const *real) {
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS_APX_BND)) return NULL;
  return new absolute_error_from_approx_bnd_scheme(real, holders[1], f);
}

// ABSOLUTE_ERROR_FROM_APPROX_ABS
REGISTER_SCHEME_BEGIN(absolute_error_from_approx_abs);
  predicated_real approx;
  function_class const *function;
  absolute_error_from_approx_abs_scheme(ast_real const *r, predicated_real const &a, function_class const *f)
    : proof_scheme(r), approx(a), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_approx_abs);

node *absolute_error_from_approx_abs_scheme::generate_proof() const {
  node *n = find_proof(approx);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->absolute_error_from_approx_abs(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect absolute_error_from_approx_abs_scheme::needed_reals() const {
  return preal_vect(1, approx);
}

proof_scheme *absolute_error_from_approx_abs_scheme::factory(ast_real const *real) {
  ast_real const *holders[2];
  function_class const *f = absolute_rounding_error(real, holders);
  if (!f || !(f->theorem_mask & function_class::TH_ABS_APX_ABS)) return NULL;
  return new absolute_error_from_approx_abs_scheme(real, predicated_real(holders[1], PRED_ABS), f);
}

// RELATIVE_ERROR
REGISTER_SCHEME_BEGIN(relative_error);
  function_class const *function;
  relative_error_scheme(predicated_real const &r, function_class const *f)
    : proof_scheme(r), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error);

node *relative_error_scheme::generate_proof() const
{
  std::string name;
  property res(real, function->relative_error(name));
  assert(is_defined(res.bnd()));
  return create_theorem(0, NULL, res, name);
}

preal_vect relative_error_scheme::needed_reals() const
{
  return preal_vect();
}

proof_scheme *relative_error_scheme::factory(predicated_real const &real)
{
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL)) return NULL;
  return new relative_error_scheme(real, f);
}

// RELATIVE_ERROR_FROM_EXACT_BND
REGISTER_SCHEME_BEGIN(relative_error_from_exact_bnd);
  function_class const *function;
  relative_error_from_exact_bnd_scheme(predicated_real const &r, function_class const *f)
    : proof_scheme(r), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error_from_exact_bnd);

node *relative_error_from_exact_bnd_scheme::generate_proof() const {
  node *n = find_proof(real.real2());
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->relative_error_from_exact_abs(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect relative_error_from_exact_bnd_scheme::needed_reals() const {
  return one_needed(real.real2());
}

proof_scheme *relative_error_from_exact_bnd_scheme::factory(predicated_real const &real) {
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL_EXA_BND)) return NULL;
  return new relative_error_from_exact_bnd_scheme(real, f);
}

// RELATIVE_ERROR_FROM_EXACT_ABS
REGISTER_SCHEME_BEGIN(relative_error_from_exact_abs);
  predicated_real exact;
  function_class const *function;
  relative_error_from_exact_abs_scheme(predicated_real const &r, predicated_real const &e, function_class const *f)
    : proof_scheme(r), exact(e), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error_from_exact_abs);

node *relative_error_from_exact_abs_scheme::generate_proof() const {
  node *n = find_proof(exact);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->relative_error_from_exact_abs(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect relative_error_from_exact_abs_scheme::needed_reals() const {
  return preal_vect(1, exact);
}

proof_scheme *relative_error_from_exact_abs_scheme::factory(predicated_real const &real) {
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL_EXA_ABS)) return NULL;
  return new relative_error_from_exact_abs_scheme(real, predicated_real(real.real2(), PRED_ABS), f);
}

// RELATIVE_ERROR_FROM_APPROX_BND
REGISTER_SCHEME_BEGIN(relative_error_from_approx_bnd);
  function_class const *function;
  relative_error_from_approx_bnd_scheme(predicated_real const &r, function_class const *f)
    : proof_scheme(r), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error_from_approx_bnd);

node *relative_error_from_approx_bnd_scheme::generate_proof() const {
  node *n = find_proof(real.real());
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->relative_error_from_approx_bnd(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect relative_error_from_approx_bnd_scheme::needed_reals() const {
  return one_needed(real.real());
}

proof_scheme *relative_error_from_approx_bnd_scheme::factory(predicated_real const &real) {
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL_APX_BND)) return NULL;
  return new relative_error_from_approx_bnd_scheme(real, f);
}

// RELATIVE_ERROR_FROM_APPROX_ABS
REGISTER_SCHEME_BEGIN(relative_error_from_approx_abs);
  predicated_real approx;
  function_class const *function;
  relative_error_from_approx_abs_scheme(predicated_real const &r, predicated_real const &a, function_class const *f)
    : proof_scheme(r), approx(a), function(f) {}
REGISTER_SCHEME_END_PREDICATE(relative_error_from_approx_abs);

node *relative_error_from_approx_abs_scheme::generate_proof() const {
  node *n = find_proof(approx);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->relative_error_from_approx_abs(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect relative_error_from_approx_abs_scheme::needed_reals() const {
  return preal_vect(1, approx);
}

proof_scheme *relative_error_from_approx_abs_scheme::factory(predicated_real const &real) {
  function_class const *f = relative_rounding_error(real);
  if (!f || !(f->theorem_mask & function_class::TH_REL_APX_ABS)) return NULL;
  return new relative_error_from_approx_abs_scheme(real, predicated_real(real.real(), PRED_ABS), f);
}

// ROUNDING_BOUND
REGISTER_SCHEME_BEGIN(rounding_bound);
  ast_real const *rounded;
  function_class const *function;
  rounding_bound_scheme(ast_real const *r, ast_real const *rr, function_class const *f)
    : proof_scheme(r), rounded(rr), function(f) {}
REGISTER_SCHEME_END(rounding_bound);

node *rounding_bound_scheme::generate_proof() const {
  node *n = find_proof(rounded);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->round(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect rounding_bound_scheme::needed_reals() const {
  return one_needed(rounded);
}

proof_scheme *rounding_bound_scheme::factory(ast_real const *real) {
  real_op const *p = boost::get < real_op const >(real);
  if (!p || !p->fun || !(p->fun->theorem_mask & function_class::TH_RND)) return NULL;
  return new rounding_bound_scheme(real, unround(p->fun->type, p->ops), p->fun);
}

// ENFORCE_BOUND
REGISTER_SCHEME_BEGIN(enforce_bound);
  function_class const *function;
  enforce_bound_scheme(ast_real const *r, function_class const *f)
    : proof_scheme(r), function(f) {}
REGISTER_SCHEME_END(enforce_bound);

node *enforce_bound_scheme::generate_proof() const {
  node *n = find_proof(real);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->enforce(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

preal_vect enforce_bound_scheme::needed_reals() const {
  return preal_vect(1, real);
}

proof_scheme *enforce_bound_scheme::factory(ast_real const *real) {
  real_op const *p = boost::get < real_op const >(real);
  if (!p || !p->fun || !(p->fun->theorem_mask & function_class::TH_ENF)) return NULL;
  return new enforce_bound_scheme(real, p->fun);
}

// COMPUTATION
REGISTER_SCHEME_BEGIN(computation);
  real_op const *naked_real;
  computation_scheme(ast_real const *r1, real_op const *r2)
    : proof_scheme(r1), naked_real(r2) {}
REGISTER_SCHEME_END(computation);

UNARY_INTERVAL(abs_updater)    { r = abs(h);    }
UNARY_INTERVAL(neg_updater)    { r = -h;        }
UNARY_INTERVAL(sqrt_updater)   { r = sqrt(h);   }
UNARY_INTERVAL(square_updater) { r = square(h); }

BINARY_INTERVAL(add_updater) { r = h[0] + h[1]; }
BINARY_INTERVAL(sub_updater) { r = h[0] - h[1]; }
BINARY_INTERVAL(mul_updater) { r = h[0] * h[1]; }
BINARY_INTERVAL(div_updater) { r = h[0] / h[1]; }

node *computation_scheme::generate_proof() const
{
  real_op const *r = naked_real;
  switch (r->ops.size()) {
  case 1: {
    node *n1 = find_proof(r->ops[0]);
    if (!n1) return NULL;
    property const &res = n1->get_result();
    interval const &i = res.bnd();
    switch (r->type) {
    case UOP_NEG:
      return create_theorem(1, &res, property(real, -i), "neg", &neg_updater);
    case UOP_SQRT:
      if (lower(i) < 0) return NULL;
      return create_theorem(1, &res, property(real, sqrt(i)), "sqrt", &sqrt_updater);
#if 0
    case UOP_ABS:
      return create_theorem(1, &res, property(real, abs(i)), std::string("abs_") += ('o' + sign(i)), &abs_updater);
#endif
    default:
      assert(false);
    }
    break; }
  case 2: {
    bool same_ops = r->ops[0] == r->ops[1];
    if (same_ops) {
      if (r->type == BOP_SUB)
        return create_theorem(0, NULL, property(real, zero()), "sub_refl", trivial_updater);
      if (r->type == BOP_DIV) {
        node *n = find_proof(predicated_real(r->ops[0], PRED_NZR));
        if (!n) return NULL;
        property const &res = n->get_result();
        number one(1);
        return create_theorem(1, &res, property(real, interval(one, one)), "div_refl");
      }
    }
    std::string s;
    node *n1 = find_proof(r->ops[0]);
    if (!n1) return NULL;
    property const &res1 = n1->get_result();
    interval const &i1 = res1.bnd();
    if (same_ops && r->type == BOP_MUL) {
      s = "square_";
      s += 'o' + sign(i1);
      return create_theorem(1, &res1, property(real, square(i1)), s, &square_updater);
    }
    node *n2 = find_proof(r->ops[1]);
    if (!n2) return NULL;
    property const &res2 = n2->get_result();
    interval const &i2 = res2.bnd();
    property res(real.real());
    interval &i = res.bnd();
    theorem_updater *u = NULL;
    switch (r->type) {
    case BOP_ADD: i = i1 + i2; s = "add"; u = &add_updater; break;
    case BOP_SUB: i = i1 - i2; s = "sub"; u = &sub_updater; break;
    case BOP_MUL:
      i = i1 * i2;
      s = "mul_";
      s += 'o' + sign(i1);
      s += 'o' + sign(i2);
      u = &mul_updater;
      break;
    case BOP_DIV:
      if (contains_zero(i2)) return NULL;
      i = i1 / i2;
      s = "div_";
      s += 'o' + sign(i1);
      s += 'o' + sign(i2);
      u = &div_updater;
      break;
    default:
      assert(false);
      return NULL;
    }
    property hyps[2] = { res1, res2 };
    return create_theorem(2, hyps, res, s, u); }
  default:
    assert(false);
  }
  return NULL;
}

preal_vect computation_scheme::needed_reals() const
{
  real_op const *r = naked_real;
  ast_real_vect const &ops = r->ops;
  if (ops.size() == 2 && ops[0] == ops[1]) {
    if (r->type == BOP_SUB) return preal_vect();
    if (r->type == BOP_DIV) return preal_vect(1, predicated_real(ops[0], PRED_NZR));
    return preal_vect(1, predicated_real(ops[0], PRED_BND));
  }
  preal_vect res;
  res.reserve(ops.size());
  for(ast_real_vect::const_iterator i = ops.begin(), end = ops.end(); i != end; ++i)
    res.push_back(predicated_real(*i, PRED_BND));
  return res;
}

proof_scheme *computation_scheme::factory(ast_real const *real)
{
  ast_real const *r = real;
  if (hidden_real const *h = boost::get< hidden_real const >(real))
    r = h->real;
  real_op const *p = boost::get< real_op const >(r);
  if (!p || p->fun || p->type == UOP_ABS) return NULL;
  return new computation_scheme(real, p);
}

// COMPUTATION_ABS
REGISTER_SCHEME_BEGIN(computation_abs);
  computation_abs_scheme(predicated_real const &r): proof_scheme(r) {}
REGISTER_SCHEME_END_PREDICATE(computation_abs);

node *computation_abs_scheme::generate_proof() const {
  real_op const *r = boost::get< real_op const >(real.real());
  assert(r);
  switch (r->ops.size()) {
  case 1: {
    node *n1 = find_proof(predicated_real(r->ops[0], PRED_ABS));
    if (!n1) return NULL;
    property const &res1 = n1->get_result();
    property res(real, res1.bnd());
    switch (r->type) {
    case UOP_NEG:
      return create_theorem(1, &res1, res, "neg_a", identity_updater);
    case UOP_ABS:
      return create_theorem(1, &res1, res, "abs_a", identity_updater);
    default:
      assert(false);
    }
    break; }
  case 2: {
    std::string s;
    node *n1 = find_proof(predicated_real(r->ops[0], PRED_ABS));
    if (!n1) return NULL;
    property const &res1 = n1->get_result();
    interval const &i1 = res1.bnd();
    node *n2 = find_proof(predicated_real(r->ops[1], PRED_ABS));
    if (!n2) return NULL;
    property const &res2 = n2->get_result();
    interval const &i2 = res2.bnd();
    property res(real);
    interval &i = res.bnd();
    theorem_updater *u = NULL;
    switch (r->type) {
    case BOP_ADD:
    case BOP_SUB:
      i = interval(lower(abs(i1 - i2)), upper(i1 + i2));
      s = (r->type == BOP_ADD) ? "add_aa" : "sub_aa";
      if (lower(i) > 0) s += (lower(i1) > upper(i2)) ? "_p" : "_n";
      else s += "_o";
      break;
    case BOP_MUL:
      i = i1 * i2;
      s = "mul_aa";
      u = &mul_updater;
      break;
    case BOP_DIV:
      if (contains_zero(i2)) return NULL;
      i = i1 / i2;
      s = "div_aa";
      u = &div_updater;
      break;
    default:
      assert(false);
      return NULL;
    }
    property hyps[2] = { res1, res2 };
    return create_theorem(2, hyps, res, s, u); }
  default:
    assert(false);
  }
  return NULL;
}

preal_vect computation_abs_scheme::needed_reals() const {
  real_op const *r = boost::get< real_op const >(real.real());
  assert(r);
  ast_real_vect const &ops = r->ops;
  preal_vect res;
  res.reserve(ops.size());
  for(ast_real_vect::const_iterator i = ops.begin(), end = ops.end(); i != end; ++i)
    res.push_back(predicated_real(*i, PRED_ABS));
  return res;
}

proof_scheme *computation_abs_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_ABS) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || p->fun || p->type == UOP_SQRT) return NULL;
  if (is_constant(real.real())) return NULL;
  return new computation_abs_scheme(real);
}

// BND_OF_ABS
REGISTER_SCHEME_BEGIN(bnd_of_abs);
  bnd_of_abs_scheme(ast_real const *r): proof_scheme(r) {}
REGISTER_SCHEME_END(bnd_of_abs);

UNARY_INTERVAL(bnd_of_abs_updater) { number const &num = upper(h); r = interval(-num, num); }

node *bnd_of_abs_scheme::generate_proof() const {
  node *n = find_proof(predicated_real(real.real(), PRED_ABS));
  if (!n) return NULL;
  property const &res1 = n->get_result();
  number const &num = upper(res1.bnd());
  property res(real, interval(-num, num));
  return create_theorem(1, &res1, res, "bnd_of_abs", &bnd_of_abs_updater);
}

preal_vect bnd_of_abs_scheme::needed_reals() const {
  return preal_vect(1, predicated_real(real.real(), PRED_ABS));
}

proof_scheme *bnd_of_abs_scheme::factory(ast_real const *real)
{
  if (is_hidden(real) || is_constant(real)) return NULL;
  real_op const *p = boost::get< real_op const >(real);
  if (p && p->type == UOP_ABS) return NULL;
  return new bnd_of_abs_scheme(real);
}

// ABS_OF_BND
REGISTER_SCHEME_BEGIN(abs_of_bnd);
  abs_of_bnd_scheme(predicated_real const &r): proof_scheme(r) {}
REGISTER_SCHEME_END_PREDICATE(abs_of_bnd);

node *abs_of_bnd_scheme::generate_proof() const
{
  node *n = find_proof(real.real());
  if (!n) return NULL;
  property const &res = n->get_result();
  interval const &i = res.bnd();
  return create_theorem(1, &res, property(real, abs(i)),
                        std::string("abs_of_bnd_") += ('o' + sign(i)), &abs_updater);
}

preal_vect abs_of_bnd_scheme::needed_reals() const
{
  return one_needed(real.real());
}

proof_scheme *abs_of_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_ABS) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (p && p->type == UOP_ABS) return NULL;
  return new abs_of_bnd_scheme(real);
}

// BND_OF_BND_ABS
REGISTER_SCHEME_BEGIN(bnd_of_bnd_abs);
  preal_vect needed;
  bnd_of_bnd_abs_scheme(preal_vect const &v) : proof_scheme(v[0]), needed(v) {}
REGISTER_SCHEME_END(bnd_of_bnd_abs);

BINARY_INTERVAL(bnd_of_bnd_abs_updater) {
  interval const &ib = h[0], &ia = h[1];
  number const &iba = lower(ib), &ibb = upper(ib), &iab = lower(ia), &iaa = -iab;
  bool b1 = iba <= iaa, b2 = iab <= ibb;
  if (b1 && b2) r = interval();
  else r = b1 ? interval(iba, iaa) : interval(iab, b2 ? ibb : iab);
}

node *bnd_of_bnd_abs_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  interval const &ib = hyps[0].bnd(), &ia = hyps[1].bnd();
  number const &iba = lower(ib), &ibb = upper(ib), &iab = lower(ia), &iaa = -iab;
  bool b1 = iba <= iaa, b2 = iab <= ibb;
  if (b1 && b2) return NULL;
  property res(real, b1 ? interval(iba, iaa) : interval(iab, b2 ? ibb : iab));
  return create_theorem(2, hyps, res, b1 ? "bnd_of_bnd_abs_n" : "bnd_of_bnd_abs_p",
                        &bnd_of_bnd_abs_updater);
}

preal_vect bnd_of_bnd_abs_scheme::needed_reals() const {
  return needed;
}

proof_scheme *bnd_of_bnd_abs_scheme::factory(ast_real const *real)
{
  if (is_hidden(real) || is_constant(real)) return NULL;
  real_op const *p = boost::get< real_op const >(real);
  if (p && p->type == UOP_ABS) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(real, PRED_BND));
  hyps.push_back(predicated_real(real, PRED_ABS));
  return new bnd_of_bnd_abs_scheme(hyps);
}

// UABS_OF_ABS
REGISTER_SCHEME_BEGIN(uabs_of_abs);
  predicated_real needed;
  uabs_of_abs_scheme(ast_real const *r, predicated_real const &v): proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END(uabs_of_abs);

node *uabs_of_abs_scheme::generate_proof() const {
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  property res(real, res1.bnd());
  return create_theorem(1, &res1, res, "uabs_of_abs", identity_updater);
}

preal_vect uabs_of_abs_scheme::needed_reals() const {
  return preal_vect(1, needed);
}

proof_scheme *uabs_of_abs_scheme::factory(ast_real const *real)
{
  real_op const *p = boost::get< real_op const >(real);
  if (!p || p->type != UOP_ABS) return NULL;
  return new uabs_of_abs_scheme(real, predicated_real(p->ops[0], PRED_ABS));
}

// ABS_OF_UABS
REGISTER_SCHEME_BEGIN(abs_of_uabs);
  predicated_real needed;
  abs_of_uabs_scheme(predicated_real const &r, predicated_real const &v): proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PREDICATE(abs_of_uabs);

node *abs_of_uabs_scheme::generate_proof() const
{
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  if (lower(res1.bnd()) < 0) return NULL;
  property res(real, res1.bnd());
  return create_theorem(1, &res1, res, "abs_of_uabs", identity_updater);
}

preal_vect abs_of_uabs_scheme::needed_reals() const
{
  return preal_vect(1, needed);
}

proof_scheme *abs_of_uabs_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_ABS) return NULL;
  ast_real const *r = real.real();
  if (is_constant(r)) return NULL;
  real_op const *p = boost::get< real_op const >(r);
  if (p && p->type == UOP_ABS) return NULL;
  ast_real const *ra = normalize(ast_real(real_op(UOP_ABS, r)));
  return new abs_of_uabs_scheme(real, predicated_real(ra, PRED_BND));
}

// NUMBER
REGISTER_SCHEME_BEGIN(number);
  number_scheme(ast_real const *r): proof_scheme(r) {}
REGISTER_SCHEME_END(number);

interval create_interval(ast_number const *, ast_number const *, bool widen = true);

node *number_scheme::generate_proof() const {
  ast_number const *const *r = boost::get< ast_number const *const >(real.real());
  assert(r);
  char const *s;
  if ((**r).base == 0 || (**r).exponent == 0) s = "constant1";
  else if ((**r).base == 2) s = "constant2";
  else s = "constant10";
  return create_theorem(0, NULL, property(real, create_interval(*r, *r)), s, trivial_updater);
}

preal_vect number_scheme::needed_reals() const {
  return preal_vect();
}

proof_scheme *number_scheme::factory(ast_real const *real) {
  if (!boost::get< ast_number const *const >(real)) return NULL;
  return new number_scheme(real);
}

// NEG_ABS_FIX_FLT
REGISTER_SCHEME_BEGIN(neg_abs_fix_flt);
  predicated_real needed;
  std::string name;
  neg_abs_fix_flt_scheme(predicated_real const &r, predicated_real const &v, std::string const &n)
    : proof_scheme(r), needed(v), name(n) {}
REGISTER_SCHEME_END_PREDICATE(neg_abs_fix_flt);

node *neg_abs_fix_flt_scheme::generate_proof() const
{
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &hyp = n->get_result();
  return create_theorem(1, &hyp, property(real, hyp.cst()), name);
}

preal_vect neg_abs_fix_flt_scheme::needed_reals() const
{
  return preal_vect(1, needed);
}

proof_scheme *neg_abs_fix_flt_scheme::factory(predicated_real const &real)
{
  predicate_type t = real.pred();
  if (t != PRED_FIX && t != PRED_FLT) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || (p->type != UOP_ABS && p->type != UOP_NEG)) return NULL;
  std::string name = p->type == UOP_ABS ? "abs_" : "neg_";
  if (is_constant(p->ops[0])) return NULL;
  return new neg_abs_fix_flt_scheme(real, predicated_real(p->ops[0], t), name + (t == PRED_FIX ? "fix" : "flt"));
}

// ADD_SUB_FIX
REGISTER_SCHEME_BEGIN(add_sub_fix);
  preal_vect needed;
  char const *name;
  add_sub_fix_scheme(predicated_real const &r, preal_vect const &v, char const *n)
    : proof_scheme(r), needed(v), name(n) {}
REGISTER_SCHEME_END_PREDICATE(add_sub_fix);

node *add_sub_fix_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  return create_theorem(2, hyps, property(real, std::min(hyps[0].cst(), hyps[1].cst())), name);
}

preal_vect add_sub_fix_scheme::needed_reals() const {
  return needed;
}

proof_scheme *add_sub_fix_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || (p->type != BOP_ADD && p->type != BOP_SUB)) return NULL;
  if (is_constant(p->ops[0]) && is_constant(p->ops[1])) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(p->ops[0], PRED_FIX));
  hyps.push_back(predicated_real(p->ops[1], PRED_FIX));
  return new add_sub_fix_scheme(real, hyps, p->type == BOP_SUB ? "sub_fix" : "add_fix");
}

// MUL_FIX_FLT
REGISTER_SCHEME_BEGIN(mul_fix_flt);
  preal_vect needed;
  char const *name;
  mul_fix_flt_scheme(predicated_real const &r, preal_vect const &v, char const *n)
    : proof_scheme(r), needed(v), name(n) {}
REGISTER_SCHEME_END_PREDICATE(mul_fix_flt);

node *mul_fix_flt_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  return create_theorem(2, hyps, property(real, hyps[0].cst() + hyps[1].cst()), name);
}

preal_vect mul_fix_flt_scheme::needed_reals() const {
  return needed;
}

proof_scheme *mul_fix_flt_scheme::factory(predicated_real const &real) {
  predicate_type t = real.pred();
  if (t != PRED_FIX && t != PRED_FLT) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || p->type != BOP_MUL) return NULL;
  if (is_constant(p->ops[0]) && is_constant(p->ops[1])) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(p->ops[0], t));
  hyps.push_back(predicated_real(p->ops[1], t));
  return new mul_fix_flt_scheme(real, hyps, t == PRED_FIX ? "mul_fix" : "mul_flt");
}

// FIX_OF_FLT_BND
REGISTER_SCHEME_BEGIN(fix_of_flt_bnd);
  preal_vect needed;
  fix_of_flt_bnd_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PREDICATE(fix_of_flt_bnd);

node *fix_of_flt_bnd_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  mpz_t m;
  mpz_init(m);
  int e, s;
  split_exact(lower(hyps[1].bnd()).data->val, m, e, s);
  if (s <= 0) { mpz_clear(m); return NULL; }
  e += mpz_sizeinbase(m, 2);
  mpz_clear(m);
  return create_theorem(2, hyps, property(real, e - hyps[0].cst()), "fix_of_flt_bnd");
}

preal_vect fix_of_flt_bnd_scheme::needed_reals() const {
  return needed;
}

proof_scheme *fix_of_flt_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_FIX) return NULL;
  ast_real const *r = real.real();
  if (is_changing_sign(r) || is_constant(r)) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(r, PRED_FLT));
  hyps.push_back(predicated_real(r, PRED_ABS));
  return new fix_of_flt_bnd_scheme(real, hyps);
}

// FLT_OF_FIX_BND
REGISTER_SCHEME_BEGIN(flt_of_fix_bnd);
  preal_vect needed;
  flt_of_fix_bnd_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PREDICATE(flt_of_fix_bnd);

node *flt_of_fix_bnd_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  mpz_t m;
  mpz_init(m);
  int e, s;
  split_exact(upper(hyps[1].bnd()).data->val, m, e, s);
  if (s <= 0) { mpz_clear(m); return NULL; }
  e += mpz_sizeinbase(m, 2);
  mpz_clear(m);
  return create_theorem(2, hyps, property(real, e - hyps[0].cst()), "flt_of_fix_bnd");
}

preal_vect flt_of_fix_bnd_scheme::needed_reals() const {
  return needed;
}

proof_scheme *flt_of_fix_bnd_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_FLT) return NULL;
  ast_real const *r = real.real();
  if (is_changing_sign(r) || is_constant(r)) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(r, PRED_FIX));
  hyps.push_back(predicated_real(r, PRED_ABS));
  return new flt_of_fix_bnd_scheme(real, hyps);
}

// FIX_OF_SINGLETON_BND
REGISTER_SCHEME_BEGIN(fix_of_singleton_bnd);
  predicated_real needed;
  fix_of_singleton_bnd_scheme(predicated_real const &r, predicated_real const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PREDICATE(fix_of_singleton_bnd);

node *fix_of_singleton_bnd_scheme::generate_proof() const {
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &hyp = n->get_result();
  interval const &i = hyp.bnd();
  number const &l = lower(i);
  if (upper(i) != l) return NULL;
  mpz_t m;
  mpz_init(m);
  int e, s;
  split_exact(l.data->val, m, e, s);
  mpz_clear(m);
  if (s == 0) return NULL;
  return create_theorem(1, &hyp, property(real, e), "fix_of_singleton_bnd");
}

preal_vect fix_of_singleton_bnd_scheme::needed_reals() const {
  return preal_vect(1, needed);
}

proof_scheme *fix_of_singleton_bnd_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  return new fix_of_singleton_bnd_scheme(real, predicated_real(real.real(), PRED_ABS));
}

// FLT_OF_SINGLETON_BND
REGISTER_SCHEME_BEGIN(flt_of_singleton_bnd);
  predicated_real needed;
  flt_of_singleton_bnd_scheme(predicated_real const &r, predicated_real const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PREDICATE(flt_of_singleton_bnd);

node *flt_of_singleton_bnd_scheme::generate_proof() const {
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &hyp = n->get_result();
  interval const &i = hyp.bnd();
  number const &l = lower(i);
  if (upper(i) != l) return NULL;
  mpz_t m;
  mpz_init(m);
  int e, s;
  split_exact(l.data->val, m, e, s);
  if (s == 0) e = 0;
  else e = mpz_sizeinbase(m, 2);
  mpz_clear(m);
  return create_theorem(1, &hyp, property(real, e), "flt_of_singleton_bnd");
}

preal_vect flt_of_singleton_bnd_scheme::needed_reals() const {
  return preal_vect(1, needed);
}

proof_scheme *flt_of_singleton_bnd_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FLT) return NULL;
  return new flt_of_singleton_bnd_scheme(real, predicated_real(real.real(), PRED_ABS));
}

// BND_OF_NZR_REL
REGISTER_SCHEME_BEGIN(bnd_of_nzr_rel);
  preal_vect needed;
  bnd_of_nzr_rel_scheme(predicated_real const &r, preal_vect const &v): proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PATTERN(bnd_of_nzr_rel,
  predicated_real((pattern(1) - pattern(0)) / pattern(0), PRED_BND));

node *bnd_of_nzr_rel_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  return create_theorem(2, hyps, property(real, hyps[1].bnd()), "bnd_of_nzr_rel", identity_updater);
}

preal_vect bnd_of_nzr_rel_scheme::needed_reals() const {
  return needed;
}

proof_scheme *bnd_of_nzr_rel_scheme::factory(predicated_real const &real,
                                             ast_real_vect const &holders)
{
  if (holders[0] == holders[1]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_NZR));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new bnd_of_nzr_rel_scheme(real, hyps);
}

// REL_OF_NZR_BND
REGISTER_SCHEME_BEGIN(rel_of_nzr_bnd);
  preal_vect needed;
  rel_of_nzr_bnd_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PREDICATE(rel_of_nzr_bnd);

node *rel_of_nzr_bnd_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  if (lower(hyps[1].bnd()) <= -1) return NULL;
  return create_theorem(2, hyps, property(real, hyps[1].bnd()), "rel_of_nzr_bnd", identity_updater);
}

preal_vect rel_of_nzr_bnd_scheme::needed_reals() const {
  return needed;
}

proof_scheme *rel_of_nzr_bnd_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_REL) return NULL;
  ast_real const *r1 = real.real(), *r2 = real.real2();
  if (r1 == r2) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(r2, PRED_NZR));
  hyps.push_back(predicated_real(normalize(real_op(
    normalize(real_op(r1, BOP_SUB, r2)), BOP_DIV, r2)), PRED_BND));
  return new rel_of_nzr_bnd_scheme(real, hyps);
}

// COMPUTATION_REL_UOP
REGISTER_SCHEME_BEGIN(computation_rel_uop);
  predicated_real needed;
  computation_rel_uop_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r), needed(n) {}
REGISTER_SCHEME_END_PREDICATE(computation_rel_uop);

node *computation_rel_uop_scheme::generate_proof() const {
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &hyp = n->get_result();
  real_op const *r = boost::get< real_op const >(real.real());
  assert(r);
  switch (r->type) {
  case UOP_NEG:
    return create_theorem(1, &hyp, hyp, "neg_r", identity_updater);
  case UOP_ABS:
    return create_theorem(1, &hyp, hyp, "abs_r", identity_updater);
  default:
    assert(false);
  }
  return NULL;
}

preal_vect computation_rel_uop_scheme::needed_reals() const {
  return preal_vect(1, needed);
}

proof_scheme *computation_rel_uop_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_REL) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || (p->type != UOP_ABS && p->type != UOP_NEG)) return NULL;
  real_op const *p2 = boost::get< real_op const >(real.real2());
  if (!p2 || p->type != p2->type) return NULL;
  return new computation_rel_uop_scheme(real, predicated_real(p->ops[0], p2->ops[0], PRED_REL));
}

// COMPUTATION_REL_ADD
REGISTER_SCHEME_BEGIN(computation_rel_add);
  preal_vect needed;
  computation_rel_add_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PREDICATE(computation_rel_add);

node *computation_rel_add_scheme::generate_proof() const {
  property hyps[4];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  property res(real, add_relative(hyps[0].bnd(), hyps[1].bnd(), hyps[2].bnd()));
  if (!is_defined(res.bnd())) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  return create_theorem(4, hyps, res, r->type == BOP_SUB ? "sub_rr" : "add_rr");
}

preal_vect computation_rel_add_scheme::needed_reals() const {
  return needed;
}

proof_scheme *computation_rel_add_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_REL) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || (p->type != BOP_ADD && p->type != BOP_SUB)) return NULL;
  ast_real const *r2 = real.real2();
  real_op const *p2 = boost::get< real_op const >(r2);
  if (!p2 || p->type != p2->type) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(p->ops[0], p2->ops[0], PRED_REL));
  hyps.push_back(predicated_real(p->ops[1], p2->ops[1], PRED_REL));
  hyps.push_back(predicated_real(normalize(real_op(p2->ops[0], BOP_DIV, r2)), PRED_BND));
  hyps.push_back(predicated_real(r2, PRED_NZR));
  return new computation_rel_add_scheme(real, hyps);
}

BINARY_INTERVAL(compose_updater) { r = compose_relative(h[0], h[1]); }

// COMPUTATION_REL_MUL
REGISTER_SCHEME_BEGIN(computation_rel_mul);
  preal_vect needed;
  computation_rel_mul_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PATTERN(computation_rel_mul,
  predicated_real(pattern(0) * pattern(1), pattern(2) * pattern(3), PRED_REL));

node *computation_rel_mul_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  property res(real, compose_relative(hyps[0].bnd(), hyps[1].bnd()));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(2, hyps, res, "mul_rr", &compose_updater);
}

preal_vect computation_rel_mul_scheme::needed_reals() const {
  return needed;
}

proof_scheme *computation_rel_mul_scheme::factory(predicated_real const &real,
                                                  ast_real_vect const &holders) {
  if (holders[0] == holders[2] || holders[1] == holders[3]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], holders[2], PRED_REL));
  hyps.push_back(predicated_real(holders[1], holders[3], PRED_REL));
  return new computation_rel_mul_scheme(real, hyps);
}

BINARY_INTERVAL(compose_inv_updater) { r = compose_relative_inv(h[0], h[1]); }

// COMPUTATION_REL_DIV
REGISTER_SCHEME_BEGIN(computation_rel_div);
  preal_vect needed;
  computation_rel_div_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PATTERN(computation_rel_div,
  predicated_real(pattern(0) / pattern(1), pattern(2) / pattern(3), PRED_REL));

node *computation_rel_div_scheme::generate_proof() const {
  property hyps[3];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  property res(real, compose_relative_inv(hyps[0].bnd(), hyps[1].bnd()));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(3, hyps, res, "div_rr", &compose_inv_updater);
}

preal_vect computation_rel_div_scheme::needed_reals() const {
  return needed;
}

proof_scheme *computation_rel_div_scheme::factory(predicated_real const &real,
                                                  ast_real_vect const &holders) {
  if (holders[0] == holders[2] || holders[1] == holders[3]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], holders[2], PRED_REL));
  hyps.push_back(predicated_real(holders[1], holders[3], PRED_REL));
  hyps.push_back(predicated_real(holders[3], PRED_NZR));
  return new computation_rel_div_scheme(real, hyps);
}

// COMPOSE_REL
REGISTER_SCHEME_BEGIN(compose_rel);
  preal_vect needed;
  compose_rel_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
 public:
  static proof_scheme *factory2(predicated_real const &, ast_real_vect const &);
REGISTER_SCHEME_END_PATTERN(compose_rel, predicated_real(pattern(1), pattern(2), PRED_REL));

node *compose_rel_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  property res(real, compose_relative(hyps[0].bnd(), hyps[1].bnd()));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(2, hyps, res, "compose", &compose_updater);
}

preal_vect compose_rel_scheme::needed_reals() const {
  return needed;
}

proof_scheme *compose_rel_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[0] == holders[2]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  hyps.push_back(predicated_real(holders[0], holders[2], PRED_REL));
  return new compose_rel_scheme(real, hyps);
}

proof_scheme *compose_rel_scheme::factory2(predicated_real const &real, ast_real_vect const &holders)
{
  if (holders[1] == holders[2]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[2], holders[1], PRED_REL));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new compose_rel_scheme(real, hyps);
}

static factory_creator compose_rel_scheme_register2(&compose_rel_scheme::factory2,
  predicated_real(pattern(2), pattern(0), PRED_REL));

// ERROR_OF_REL
REGISTER_SCHEME_BEGIN(error_of_rel);
  preal_vect needed;
  error_of_rel_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PATTERN(error_of_rel, predicated_real(pattern(1) - pattern(0), PRED_BND));

node *error_of_rel_scheme::generate_proof() const {
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  interval const &i1 = hyps[0].bnd(), &i2 = hyps[1].bnd();
  property res(real, i1 * i2);
  std::string s = "error_of_rel_";
  s += 'o' + sign(i1);
  s += 'o' + sign(i2);
  return create_theorem(2, hyps, res, s, &mul_updater);
}

preal_vect error_of_rel_scheme::needed_reals() const {
  return needed;
}

proof_scheme *error_of_rel_scheme::factory(predicated_real const &real,
                                           ast_real_vect const &holders) {
  if (holders[0] == holders[1]) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  hyps.push_back(predicated_real(holders[0], PRED_BND));
  return new error_of_rel_scheme(real, hyps);
}

// REL_OF_EQUAL
REGISTER_SCHEME_BEGIN(rel_of_equal);
  ast_real const *needed;
  rel_of_equal_scheme(predicated_real const &r, ast_real const *n)
    : proof_scheme(r), needed(n) {}
REGISTER_SCHEME_END_PREDICATE(rel_of_equal);

node *rel_of_equal_scheme::generate_proof() const
{
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &hyp = n->get_result();
  if (!is_zero(hyp.bnd())) return NULL;
  return create_theorem(1, &hyp, property(real, hyp.bnd()), "rel_of_equal", trivial_updater);
}

preal_vect rel_of_equal_scheme::needed_reals() const
{
  return one_needed(needed);
}

proof_scheme *rel_of_equal_scheme::factory(predicated_real const &real)
{
  if (real.pred() != PRED_REL) return NULL;
  ast_real const *r = normalize(real_op(real.real(), BOP_SUB, real.real2()));
  return new rel_of_equal_scheme(real, r);
}

// NZR_OF_ABS
REGISTER_SCHEME_BEGIN(nzr_of_abs);
  predicated_real needed;
  nzr_of_abs_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r), needed(n) {}
REGISTER_SCHEME_END_PREDICATE(nzr_of_abs);

node *nzr_of_abs_scheme::generate_proof() const {
  node *n = find_proof(needed);
  if (!n) return NULL;
  property const &hyp = n->get_result();
  if (contains_zero(hyp.bnd())) return NULL;
  return create_theorem(1, &hyp, property(real), "nzr_of_abs", trivial_updater);
}

preal_vect nzr_of_abs_scheme::needed_reals() const {
  return preal_vect(1, needed);
}

proof_scheme *nzr_of_abs_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_NZR) return NULL;
  return new nzr_of_abs_scheme(real, predicated_real(real.real(), PRED_ABS));
}

// NZR_OF_UNCONSTRAINED
REGISTER_SCHEME_BEGIN(nzr_of_unconstrained);
  nzr_of_unconstrained_scheme(predicated_real const &r): proof_scheme(r) {}
REGISTER_SCHEME_END_PREDICATE(nzr_of_unconstrained);

node *nzr_of_unconstrained_scheme::generate_proof() const
{
  return create_theorem(0, NULL, property(real), "$FALSE");
}

preal_vect nzr_of_unconstrained_scheme::needed_reals() const
{
  return preal_vect();
}

proof_scheme *nzr_of_unconstrained_scheme::factory(predicated_real const &real)
{
  extern bool parameter_constrained;
  if (real.pred() != PRED_NZR || parameter_constrained) return NULL;
  return new nzr_of_unconstrained_scheme(real);
}

// NZR_OF_NZR_REL
REGISTER_SCHEME_BEGIN(nzr_of_nzr_rel);
  preal_vect needed;
  nzr_of_nzr_rel_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PATTERN(nzr_of_nzr_rel, predicated_real(pattern(1), PRED_NZR));

node *nzr_of_nzr_rel_scheme::generate_proof() const
{
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  return create_theorem(2, hyps, real, "nzr_of_nzr_rel");
}

preal_vect nzr_of_nzr_rel_scheme::needed_reals() const
{
  return needed;
}

proof_scheme *nzr_of_nzr_rel_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[0], PRED_NZR));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new nzr_of_nzr_rel_scheme(real, hyps);
}

// NZR_OF_NZR_REL_REV
REGISTER_SCHEME_BEGIN(nzr_of_nzr_rel_rev);
  preal_vect needed;
  nzr_of_nzr_rel_rev_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PATTERN(nzr_of_nzr_rel_rev, predicated_real(pattern(-1), PRED_NZR));

node *nzr_of_nzr_rel_rev_scheme::generate_proof() const
{
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  return create_theorem(2, hyps, real, "nzr_of_nzr_rel_rev");
}

preal_vect nzr_of_nzr_rel_rev_scheme::needed_reals() const
{
  return needed;
}

proof_scheme *nzr_of_nzr_rel_rev_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  hyps.push_back(predicated_real(holders[1], PRED_NZR));
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  return new nzr_of_nzr_rel_rev_scheme(real, hyps);
}

// BND_DIV_OF_REL_BND_DIV
REGISTER_SCHEME_BEGIN(bnd_div_of_rel_bnd_div);
  preal_vect needed;
  bnd_div_of_rel_bnd_div_scheme(predicated_real const &r, preal_vect const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEME_END_PATTERN(bnd_div_of_rel_bnd_div, predicated_real((pattern(1) - pattern(0)) / pattern(2), PRED_BND));

node *bnd_div_of_rel_bnd_div_scheme::generate_proof() const
{
  property hyps[2];
  if (!fill_hypotheses(hyps, needed)) return NULL;
  property res(real, hyps[0].bnd() * hyps[1].bnd());
  return create_theorem(2, hyps, res, "bnd_div_of_rel_bnd_div", &mul_updater);
}

preal_vect bnd_div_of_rel_bnd_div_scheme::needed_reals() const
{
  return needed;
}

proof_scheme *bnd_div_of_rel_bnd_div_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  preal_vect hyps;
  if (holders[0] == holders[2]) return NULL;
  hyps.push_back(predicated_real(holders[1], holders[0], PRED_REL));
  hyps.push_back(predicated_real(normalize(real_op(holders[0], BOP_DIV, holders[2])), PRED_BND));
  return new bnd_div_of_rel_bnd_div_scheme(real, hyps);
}
