#include "backends/backend.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/proof_graph.hpp"

extern pattern absolute_error_pattern, relative_error_pattern;
extern backend *display;

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

ast_real_vect absolute_error_scheme::needed_reals() const {
  return ast_real_vect();
}

proof_scheme *absolute_error_scheme::factory(ast_real const *real) {
  ast_real_vect holders(2);
  if (!match(real, absolute_error_pattern, holders)) return NULL;
  real_op const *p = boost::get < real_op const >(holders[1]);
  assert(p && p->fun);
  if (!(p->fun->theorem_mask & function_class::TH_ABS)) return NULL;
  return new absolute_error_scheme(real, p->fun);
}

// ABSOLUTE_ERROR_FROM_REAL
REGISTER_SCHEME_BEGIN(absolute_error_from_real);
  ast_real const *rounded;
  function_class const *function;
  absolute_error_from_real_scheme(ast_real const *r, ast_real const *rr, function_class const *f)
    : proof_scheme(r), rounded(rr), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_real);

node *absolute_error_from_real_scheme::generate_proof() const {
  node *n = find_proof(rounded);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->absolute_error_from_real(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

ast_real_vect absolute_error_from_real_scheme::needed_reals() const {
  return ast_real_vect(1, rounded);
}

proof_scheme *absolute_error_from_real_scheme::factory(ast_real const *real) {
  ast_real_vect holders(2);
  if (!match(real, absolute_error_pattern, holders)) return NULL;
  real_op const *p = boost::get < real_op const >(holders[1]);
  assert(p && p->fun);
  if (!(p->fun->theorem_mask & function_class::TH_ABS_REA)) return NULL;
  return new absolute_error_from_real_scheme(real, holders[0], p->fun);
}

// ABSOLUTE_ERROR_FROM_ROUNDED
REGISTER_SCHEME_BEGIN(absolute_error_from_rounded);
  ast_real const *approx;
  function_class const *function;
  absolute_error_from_rounded_scheme(ast_real const *r, ast_real const *a, function_class const *f)
    : proof_scheme(r), approx(a), function(f) {}
REGISTER_SCHEME_END(absolute_error_from_rounded);

node *absolute_error_from_rounded_scheme::generate_proof() const {
  node *n = find_proof(approx);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->absolute_error_from_rounded(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

ast_real_vect absolute_error_from_rounded_scheme::needed_reals() const {
  return ast_real_vect(1, approx);
}

proof_scheme *absolute_error_from_rounded_scheme::factory(ast_real const *real) {
  ast_real_vect holders(2);
  if (!match(real, absolute_error_pattern, holders)) return NULL;
  real_op const *p = boost::get < real_op const >(holders[1]);
  assert(p && p->fun);
  if (!(p->fun->theorem_mask & function_class::TH_ABS_RND)) return NULL;
  return new absolute_error_from_rounded_scheme(real, holders[1], p->fun);
}

// RELATIVE_ERROR_FROM_REAL
REGISTER_SCHEME_BEGIN(relative_error_from_real);
  ast_real const *absval;
  function_class const *function;
  relative_error_from_real_scheme(ast_real const *r, ast_real const *a, function_class const *f)
    : proof_scheme(r), absval(a), function(f) {}
REGISTER_SCHEME_END(relative_error_from_real);

node *relative_error_from_real_scheme::generate_proof() const {
  node *n = find_proof(absval);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->relative_error_from_real(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

ast_real_vect relative_error_from_real_scheme::needed_reals() const {
  return ast_real_vect(1, absval);
}

proof_scheme *relative_error_from_real_scheme::factory(ast_real const *real) {
  ast_real_vect holders(2);
  if (!match(real, relative_error_pattern, holders)) return NULL;
  real_op const *p = boost::get < real_op const >(holders[1]);
  assert(p && p->fun);
  if (!(p->fun->theorem_mask & function_class::TH_REL_REA)) return NULL;
  ast_real const *av = normalize(ast_real(real_op(UOP_ABS, holders[0])));
  return new relative_error_from_real_scheme(real, av, p->fun);
}

// RELATIVE_ERROR_FROM_ROUNDED
REGISTER_SCHEME_BEGIN(relative_error_from_rounded);
  ast_real const *absval;
  function_class const *function;
  relative_error_from_rounded_scheme(ast_real const *r, ast_real const *a, function_class const *f)
    : proof_scheme(r), absval(a), function(f) {}
REGISTER_SCHEME_END(relative_error_from_rounded);

node *relative_error_from_rounded_scheme::generate_proof() const {
  node *n = find_proof(absval);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  std::string name;
  property res(real, function->relative_error_from_rounded(res1.bnd(), name));
  if (!is_defined(res.bnd())) return NULL;
  return create_theorem(1, &res1, res, name);
}

ast_real_vect relative_error_from_rounded_scheme::needed_reals() const {
  return ast_real_vect(1, absval);
}

proof_scheme *relative_error_from_rounded_scheme::factory(ast_real const *real) {
  ast_real_vect holders(2);
  if (!match(real, relative_error_pattern, holders)) return NULL;
  real_op const *p = boost::get < real_op const >(holders[1]);
  assert(p && p->fun);
  if (!(p->fun->theorem_mask & function_class::TH_REL_RND)) return NULL;
  ast_real const *av = normalize(ast_real(real_op(UOP_ABS, holders[0])));
  return new relative_error_from_rounded_scheme(real, av, p->fun);
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

ast_real_vect rounding_bound_scheme::needed_reals() const {
  return ast_real_vect(1, rounded);
}

proof_scheme *rounding_bound_scheme::factory(ast_real const *real) {
  function_class const *f;
  ast_real const *r = morph(real, &f);
  if (!r || !(f->theorem_mask & function_class::TH_RND)) return NULL;
  return new rounding_bound_scheme(real, r, f);
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

ast_real_vect enforce_bound_scheme::needed_reals() const {
  return ast_real_vect(1, real);
}

proof_scheme *enforce_bound_scheme::factory(ast_real const *real) {
  function_class const *f;
  if (!morph(real, &f) || !(f->theorem_mask & function_class::TH_ENF)) return NULL;
  return new enforce_bound_scheme(real, f);
}

// COMPUTATION
REGISTER_SCHEME_BEGIN(computation);
  computation_scheme(ast_real const *r): proof_scheme(r) {}
REGISTER_SCHEME_END(computation);

node *computation_scheme::generate_proof() const {
  real_op const *r = boost::get< real_op const >(real);
  assert(r);
  switch (r->ops.size()) {
  case 1: {
    node *n1 = find_proof(r->ops[0]);
    if (!n1) return NULL;
    property const &res = n1->get_result();
    interval const &i = res.bnd();
    switch (r->type) {
    case UOP_NEG:
      return create_theorem(1, &res, property(real, -i), "neg");
    case UOP_ABS:
      return create_theorem(1, &res, property(real, abs(i)), std::string("abs_") += ('o' + sign(i)));
    default:
      assert(false);
    }
    break; }
  case 2: {
    bool same_ops = r->ops[0] == r->ops[1];
    if (same_ops && r->type == BOP_SUB)
      return create_theorem(0, NULL, property(real, zero()), "sub_refl");
    std::string s;
    node *n1 = find_proof(r->ops[0]);
    if (!n1) return NULL;
    property const &res1 = n1->get_result();
    interval const &i1 = res1.bnd();
    if (same_ops && r->type == BOP_MUL) {
      s = "square_";
      s += 'o' + sign(i1);
      return create_theorem(1, &res1, property(real, square(i1)), s);
    }
    node *n2 = find_proof(r->ops[1]);
    if (!n2) return NULL;
    property const &res2 = n2->get_result();
    interval const &i2 = res2.bnd();
    property res(real);
    interval &i = res.bnd();
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
      s = "div_";
      s += 'o' + sign(i1);
      s += 'o' + sign(i2);
      break;
    default:
      assert(false);
      return NULL;
    }
    property hyps[2] = { res1, res2 };
    return create_theorem(2, hyps, res, s); }
  default:
    assert(false);
  }
  return NULL;
}

ast_real_vect computation_scheme::needed_reals() const {
  real_op const *r = boost::get< real_op const >(real);
  assert(r);
  if (r->type == BOP_SUB && r->ops[0] == r->ops[1])
    return ast_real_vect(); // special case, x-x is always 0
  return r->ops;
}

proof_scheme *computation_scheme::factory(ast_real const *real) {
  real_op const *p = boost::get< real_op const >(real);
  if (!p || p->fun) return NULL;
  return new computation_scheme(real);
}

// INVERT_ABS
REGISTER_SCHEME_BEGIN(invert_abs);
  ast_real const *absval;
  invert_abs_scheme(ast_real const *r, ast_real const *a): proof_scheme(r), absval(a) {}
REGISTER_SCHEME_END(invert_abs);

node *invert_abs_scheme::generate_proof() const {
  node *n = find_proof(absval);
  if (!n) return NULL;
  property const &res1 = n->get_result();
  number const &num = upper(res1.bnd());
  property res(real, interval(-num, num));
  return create_theorem(1, &res1, res, "invert_abs");
}

ast_real_vect invert_abs_scheme::needed_reals() const {
  return ast_real_vect(1, absval);
}

proof_scheme *invert_abs_scheme::factory(ast_real const *real) {
  if (real_op const *r = boost::get< real_op const >(real))
    if (r->type == UOP_ABS) return NULL;
  ast_real const *av = normalize(ast_real(real_op(UOP_ABS, real)));
  return new invert_abs_scheme(real, av);
}

// ABS_MUL
static proof_scheme *abs_mul_scheme_factory(ast_real const *real) {
  std::string s = "abs_mul_";
  real_op const *r = boost::get< real_op const >(real);
  if (!r || r->type != UOP_ABS) return NULL;
  real_op const *rr = boost::get< real_op const >(r->ops[0]);
  if (!rr || rr->type != BOP_MUL) return NULL;
  ast_real const *r1 = rr->ops[0], *r2 = rr->ops[1], *r3 = NULL, *r4 = NULL;
  if (real_op const *r = boost::get< real_op const >(r1))
    if (r->type == UOP_ABS) r3 = r1;
  if (real_op const *r = boost::get< real_op const >(r2))
    if (r->type == UOP_ABS) r4 = r2;
  if (!r3) {
    r3 = normalize(ast_real(real_op(UOP_ABS, r1)));
    s += 'x';
  } else s += 'a';
  if (!r4) {
    r4 = normalize(ast_real(real_op(UOP_ABS, r2)));
    s += 'x';
  } else s += 'a';
  ast_real const *res = normalize(ast_real(real_op(r3, BOP_MUL, r4)));
  return new rewrite_scheme(real, res, s);
}

static scheme_register abs_mul_scheme_register(&abs_mul_scheme_factory);

// COMPOSE RELATIVE
REGISTER_SCHEME_BEGIN(compose_relative);
  compose_relative_scheme(ast_real const *r): proof_scheme(r) {}
REGISTER_SCHEME_END(compose_relative);

node *compose_relative_scheme::generate_proof() const {
  real_op const *r = boost::get< real_op const >(real);
  assert(r && r->type == BOP_ADD);
  real_op const *r1 = boost::get< real_op const >(r->ops[0]),
                *r2 = boost::get< real_op const >(r->ops[1]);
  assert(r1 && r2 && r1->type == BOP_ADD && r2->type == BOP_MUL
         && r1->ops[0] == r2->ops[0] && r1->ops[1] == r2->ops[1]);
  node *n1 = find_proof(r1->ops[0]), *n2 = find_proof(r1->ops[1]);
  if (!n1 || !n2) return NULL;
  property const &res1 = n1->get_result(), &res2 = n2->get_result();
  property res(real, compose_relative(res1.bnd(), res2.bnd()));
  if (!is_defined(res.bnd())) return NULL;
  property hyps[2] = { res1, res2 };
  return create_theorem(2, hyps, res, "compose");
}

ast_real_vect compose_relative_scheme::needed_reals() const {
  real_op const *r = boost::get< real_op const >(real);
  assert(r && r->type == BOP_ADD);
  real_op const *r1 = boost::get< real_op const >(r->ops[0]),
                *r2 = boost::get< real_op const >(r->ops[1]);
  assert(r1 && r2 && r1->type == BOP_ADD && r2->type == BOP_MUL
         && r1->ops[0] == r2->ops[0] && r1->ops[1] == r2->ops[1]);
  return r1->ops;
}

proof_scheme *compose_relative_scheme::factory(ast_real const *real) {
  real_op const *r = boost::get< real_op const >(real);
  if (!r || r->type != BOP_ADD) return NULL;
  real_op const *r1 = boost::get< real_op const >(r->ops[0]),
                *r2 = boost::get< real_op const >(r->ops[1]);
  if (!r1 || !r2 || r1->type != BOP_ADD || r2->type != BOP_MUL
      || r1->ops[0] != r2->ops[0] || r1->ops[1] != r2->ops[1])
    return NULL;
  return new compose_relative_scheme(real);
}

// NUMBER
REGISTER_SCHEME_BEGIN(number);
  number_scheme(ast_real const *r): proof_scheme(r) {}
REGISTER_SCHEME_END(number);

interval create_interval(ast_interval const &, bool widen = true);

node *number_scheme::generate_proof() const {
  ast_number const *const *r = boost::get< ast_number const *const >(real);
  assert(r);
  ast_interval _i = { *r, *r };
  char const *s;
  if ((**r).base == 0 || (**r).exponent == 0) s = "constant1";
  else if ((**r).base == 2) s = "constant2";
  else s = "constant10";
  return create_theorem(0, NULL, property(real, create_interval(_i)), s);
}

ast_real_vect number_scheme::needed_reals() const {
  return ast_real_vect();
}

proof_scheme *number_scheme::factory(ast_real const *real) {
  if (!boost::get< ast_number const *const >(real)) return NULL;
  return new number_scheme(real);
}

// REWRITE
ast_real_vect rewrite_scheme::needed_reals() const {
  ast_real_vect res(1, rewritten);
  for(pattern_cond_vect::const_iterator i = conditions.begin(), end = conditions.end();
      i != end; ++i)
    res.push_back(i->real);
  return res;
}

node *rewrite_scheme::generate_proof() const {
  node *n = find_proof(rewritten);
  if (!n) return NULL;
  std::vector< property > hyps;
  for(pattern_cond_vect::const_iterator i = conditions.begin(), end = conditions.end();
      i != end; ++i) {
    node *m = find_proof(i->real);
    if (!m) return NULL;
    property const &res = m->get_result();
    interval const &b = res.bnd();
    number n(i->value);
    bool good;
    switch (i->type) {
    case COND_LE: good = n >= upper(b); break;
    case COND_GE: good = n <= lower(b); break;
    case COND_LT: good = n > upper(b); break;
    case COND_GT: good = n < lower(b); break;
    case COND_NE: good = n > upper(b) || n < lower(b); break;
    default: assert(false);
    }
    if (!good) return NULL;
    hyps.push_back(res);
  }
  property const &res = n->get_result();
  hyps.push_back(res);
  return create_theorem(hyps.size(), &*hyps.begin(), property(real, res.bnd()), name);
}

struct rewrite_factory: scheme_factory {
  ast_real const *src, *dst;
  std::string name;
  rewrite_factory(ast_real const *q1, ast_real const *q2)
    : src(q1), dst(q2), name(display->rewrite(src, dst)) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *rewrite_factory::operator()(ast_real const *r) const {
  if (r != src) return NULL;
  return new rewrite_scheme(src, dst, name);
}

void register_user_rewrite(ast_real const *r1, ast_real const *r2) {
  scheme_register dummy(new rewrite_factory(r1, r2));
}
