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

static preal_vect one_needed(ast_real const *r) {
  return preal_vect(1, predicated_real(r, PRED_BND));
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

preal_vect absolute_error_from_real_scheme::needed_reals() const {
  return one_needed(rounded);
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

preal_vect absolute_error_from_rounded_scheme::needed_reals() const {
  return one_needed(approx);
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

preal_vect relative_error_from_real_scheme::needed_reals() const {
  return one_needed(absval);
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

preal_vect relative_error_from_rounded_scheme::needed_reals() const {
  return one_needed(absval);
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

preal_vect rounding_bound_scheme::needed_reals() const {
  return one_needed(rounded);
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

preal_vect enforce_bound_scheme::needed_reals() const {
  return preal_vect(1, real);
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
  real_op const *r = boost::get< real_op const >(real.real());
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
    property res(real.real());
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

preal_vect computation_scheme::needed_reals() const {
  real_op const *r = boost::get< real_op const >(real.real());
  assert(r);
  ast_real_vect const &ops = r->ops;
  if (r->type == BOP_SUB && ops[0] == ops[1])
    return preal_vect(); // special case, x-x is always 0
  preal_vect res;
  res.reserve(ops.size());
  for(ast_real_vect::const_iterator i = ops.begin(), end = ops.end(); i != end; ++i)
    res.push_back(predicated_real(*i, PRED_BND));
  return res;
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

preal_vect invert_abs_scheme::needed_reals() const {
  return one_needed(absval);
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
  real_op const *r = boost::get< real_op const >(real.real());
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

preal_vect compose_relative_scheme::needed_reals() const {
  real_op const *r = boost::get< real_op const >(real.real());
  assert(r && r->type == BOP_ADD);
  real_op const *r1 = boost::get< real_op const >(r->ops[0]),
                *r2 = boost::get< real_op const >(r->ops[1]);
  assert(r1 && r2 && r1->type == BOP_ADD && r2->type == BOP_MUL
         && r1->ops[0] == r2->ops[0] && r1->ops[1] == r2->ops[1]);
  preal_vect res;
  res.push_back(predicated_real(r1->ops[0], PRED_BND));
  res.push_back(predicated_real(r1->ops[1], PRED_BND));
  return res;
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
  ast_number const *const *r = boost::get< ast_number const *const >(real.real());
  assert(r);
  ast_interval _i = { *r, *r };
  char const *s;
  if ((**r).base == 0 || (**r).exponent == 0) s = "constant1";
  else if ((**r).base == 2) s = "constant2";
  else s = "constant10";
  return create_theorem(0, NULL, property(real, create_interval(_i)), s);
}

preal_vect number_scheme::needed_reals() const {
  return preal_vect();
}

proof_scheme *number_scheme::factory(ast_real const *real) {
  if (!boost::get< ast_number const *const >(real)) return NULL;
  return new number_scheme(real);
}

// REWRITE
preal_vect rewrite_scheme::needed_reals() const {
  preal_vect res = one_needed(rewritten);
  for(pattern_cond_vect::const_iterator i = conditions.begin(), end = conditions.end();
      i != end; ++i)
    res.push_back(predicated_real(i->real, PRED_BND));
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
  virtual proof_scheme *operator()(predicated_real const &) const;
};

proof_scheme *rewrite_factory::operator()(predicated_real const &r) const {
  if (r.pred() != PRED_BND || r.real() != src) return NULL;
  return new rewrite_scheme(src, dst, name);
}

void register_user_rewrite(ast_real const *r1, ast_real const *r2) {
  scheme_register dummy(new rewrite_factory(r1, r2));
}

// ADD_SUB_FIX
REGISTER_SCHEMEX_BEGIN(add_sub_fix);
  preal_vect needed;
  char const *name;
  add_sub_fix_scheme(predicated_real const &r, preal_vect &v, char const *n)
    : proof_scheme(r), needed(v), name(n) {}
REGISTER_SCHEMEX_END(add_sub_fix);

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
  preal_vect hyps;
  hyps.push_back(predicated_real(p->ops[0], PRED_FIX));
  hyps.push_back(predicated_real(p->ops[1], PRED_FIX));
  return new add_sub_fix_scheme(real, hyps, p->type == BOP_SUB ? "sub_fix" : "add_fix");
}

// MUL_FIX_FLT
REGISTER_SCHEMEX_BEGIN(mul_fix_flt);
  preal_vect needed;
  char const *name;
  mul_fix_flt_scheme(predicated_real const &r, preal_vect &v, char const *n)
    : proof_scheme(r), needed(v), name(n) {}
REGISTER_SCHEMEX_END(mul_fix_flt);

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
  if (t == PRED_BND) return NULL;
  real_op const *p = boost::get< real_op const >(real.real());
  if (!p || p->type != BOP_MUL) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(p->ops[0], t));
  hyps.push_back(predicated_real(p->ops[1], t));
  return new mul_fix_flt_scheme(real, hyps, t == PRED_FIX ? "mul_fix" : "mul_flt");
}

// FIX_OF_FLT_BND
REGISTER_SCHEMEX_BEGIN(fix_of_flt_bnd);
  preal_vect needed;
  fix_of_flt_bnd_scheme(predicated_real const &r, preal_vect &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEMEX_END(fix_of_flt_bnd);

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

proof_scheme *fix_of_flt_bnd_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(real.real(), PRED_FLT));
  hyps.push_back(predicated_real(normalize(ast_real(real_op(UOP_ABS, real.real()))), PRED_BND));
  return new fix_of_flt_bnd_scheme(real, hyps);
}

// FLT_OF_FIX_BND
REGISTER_SCHEMEX_BEGIN(flt_of_fix_bnd);
  preal_vect needed;
  flt_of_fix_bnd_scheme(predicated_real const &r, preal_vect &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEMEX_END(flt_of_fix_bnd);

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

proof_scheme *flt_of_fix_bnd_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FLT) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(real.real(), PRED_FIX));
  hyps.push_back(predicated_real(normalize(ast_real(real_op(UOP_ABS, real.real()))), PRED_BND));
  return new flt_of_fix_bnd_scheme(real, hyps);
}

// FIX_OF_SINGLETON_BND
REGISTER_SCHEMEX_BEGIN(fix_of_singleton_bnd);
  predicated_real needed;
  fix_of_singleton_bnd_scheme(predicated_real const &r, predicated_real const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEMEX_END(fix_of_singleton_bnd);

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
  return new fix_of_singleton_bnd_scheme(real, predicated_real(real.real(), PRED_BND));
}

// FLT_OF_SINGLETON_BND
REGISTER_SCHEMEX_BEGIN(flt_of_singleton_bnd);
  predicated_real needed;
  flt_of_singleton_bnd_scheme(predicated_real const &r, predicated_real const &v)
    : proof_scheme(r), needed(v) {}
REGISTER_SCHEMEX_END(flt_of_singleton_bnd);

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
  return new flt_of_singleton_bnd_scheme(real, predicated_real(real.real(), PRED_BND));
}
