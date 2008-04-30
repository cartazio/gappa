#include <iostream>
#include <boost/preprocessor/cat.hpp>
#include "backends/backend.hpp"
#include "numbers/real.hpp"
#include "numbers/interval.hpp"
#include "numbers/interval_utility.hpp"
#include "parser/ast.hpp"
#include "proofs/rewriting.hpp"
#include "proofs/updater.hpp"

extern backend *proof_generator;
extern bool parameter_constrained;

// REWRITING_SCHEME
struct rewriting_scheme: proof_scheme {
  predicated_real rewritten;
  std::string name;
  pattern_cond_vect conditions;
  rewriting_scheme(predicated_real const &src, predicated_real const &dst,
                   std::string const &n, pattern_cond_vect const &c)
    : proof_scheme(src), rewritten(dst), name(n), conditions(c) {}
  virtual node *generate_proof() const;
  virtual preal_vect needed_reals() const;
};

preal_vect rewriting_scheme::needed_reals() const
{
  preal_vect res(1, rewritten);
  for (pattern_cond_vect::const_iterator i = conditions.begin(),
       end = conditions.end(); i != end; ++i)
    res.push_back(predicated_real(i->real, i->type == COND_NZ ? PRED_NZR : PRED_BND));
  return res;
}

node *rewriting_scheme::generate_proof() const {
  node *n = find_proof(rewritten);
  if (!n) return NULL;
  std::vector< property > hyps;
  for (pattern_cond_vect::const_iterator i = conditions.begin(),
       i_end = conditions.end(); i != i_end; ++i)
  {
    if (i->type == COND_NZ)
    {
      node *m = find_proof(predicated_real(i->real, PRED_NZR));
      if (!m) return NULL;
      hyps.push_back(m->get_result());
      continue;
    }
    property p(predicated_real(i->real, PRED_BND));
    number n(i->value);
    switch (i->type)
    {
      case COND_LE:
      case COND_LT:
        p.bnd() = interval(number::neg_inf, n); break;
      case COND_GE:
      case COND_GT:
        p.bnd() = interval(n, number::pos_inf); break;
      case COND_NE: break;
      default: assert(false);
    }
    if (node *m = find_proof(p))
    {
      property const &res = m->get_result();
      interval const &b = res.bnd();
      bool good = true;
      switch(i->type)
      {
        case COND_LT: good = n > upper(b); break;
        case COND_GT: good = n < lower(b); break;
        case COND_NE: good = n > upper(b) || n < lower(b); break;
        default: ;
      }
      if (good)
      {
        hyps.push_back(res);
        continue;
      }
    }
    if (parameter_constrained) return NULL;
    hyps.push_back(p);
  }
  property const &res = n->get_result();
  hyps.push_back(res);
  return create_theorem(hyps.size(), &*hyps.begin(), property(real, res.bnd()),
                        name, identity_updater);
}

// REWRITING_FACTORY
struct rewriting_factory: scheme_factory
{
  predicated_real dst;
  std::string name;
  rewriting_rule const *rule;
  pattern_cond_vect cond;
  virtual proof_scheme *operator()(predicated_real const &, ast_real_vect const &) const;
  rewriting_factory(predicated_real const &p1, predicated_real const &p2,
                    std::string const &n, rewriting_rule const *r)
    : scheme_factory(p1), dst(p2), name(n), rule(r), cond() {}
  rewriting_factory(predicated_real const &p1, predicated_real const &p2,
                    std::string const &n, pattern_cond_vect const &c)
    : scheme_factory(p1), dst(p2), name(n), rule(NULL), cond(c) {}
};

proof_scheme *rewriting_factory::operator()(predicated_real const &src,
                                            ast_real_vect const &holders) const
{
  if (!rule)
  {
    // user-defined rule, no placeholders nor exclusions
    assert(holders.empty());
    return new rewriting_scheme(src, dst, name, cond);
  }

  // hard-coded rule
  predicate_type t = dst.pred();
  ast_real const *r = rewrite(dst.real(), holders);

  predicated_real d = t == PRED_REL
    ? predicated_real(r, rewrite(dst.real2(), holders), t)
    : predicated_real(r, t);

  for (pattern_excl_vect::const_iterator i = rule->excl.begin(),
       i_end = rule->excl.end(); i != i_end; ++i)
  {
    if (rewrite(i->first, holders) == rewrite(i->second, holders))
      return NULL;
  }

  pattern_cond_vect c(rule->cond);
  for (pattern_cond_vect::iterator i = c.begin(), end = c.end(); i != end; ++i)
    i->real = rewrite(i->real, holders);
  return new rewriting_scheme(src, d, name, c);
}

void register_user_rewrite(ast_real const *r1, ast_real const *r2, hint_cond_vect *hc)
{
  pattern_cond_vect pc;
  if (hc)
  {
    for (hint_cond_vect::const_iterator i = hc->begin(),
         i_end = hc->end(); i != i_end; ++i)
    {
      hint_cond const *c = *i;
      pattern_cond cond;
      cond.real = c->real;
      cond.value = atoi(c->value->mantissa.c_str());
      cond.type = c->type == COND_NE && cond.value == 0 ? COND_NZ : c->type;
      pc.push_back(cond);
      delete c;
    }
  }
  std::string name = proof_generator ? proof_generator->rewrite(r1, r2, pc) : "$AXIOM";
  predicated_real p1(r1, PRED_BND), p2(r2, PRED_BND);
  new rewriting_factory(p1, p2, name, pc);
}

// REWRITING_RULE
rewriting_vect rewriting_rules;

rewriting_rule::rewriting_rule
  (ast_real const *r1, ast_real const *r2, std::string const &n,
   pattern_cond_vect const &c, pattern_excl_vect const &e)
  : src(r1), dst(r2), cond(c), excl(e)
{
  rewriting_rules.push_back(this);
  predicated_real p1(r1, PRED_BND), p2(r2, PRED_BND);
  ast_real const *h1[2], *h2[2];
  if (relative_error(r1, h1) && relative_error(r2, h2))
  {
    p1 = predicated_real(h1[1], h1[0], PRED_REL);
    p2 = predicated_real(h2[1], h2[0], PRED_REL);
  }
  new rewriting_factory(p1, p2, n, this);
}

// PATTERN OPERATIONS
pattern_cond_vect operator&&(pattern_cond_vect const &v, pattern_cond const &c) {
  pattern_cond_vect res(v);
  res.push_back(c);
  return res;
}

pattern_excl operator^(pattern const &a, pattern const &b) {
  return pattern_excl(a, b);
}

pattern_excl_vect operator&&(pattern_excl_vect const &v, pattern_excl const &c) {
  pattern_excl_vect res(v);
  res.push_back(c);
  return res;
}

static pattern a(0), b(1), c(2), d(3), a_b(-1), one(token_one);

#define abs pattern::abs
#define sqrt pattern::sqrt
#define hide pattern::hide

#define REWRITING_NAME BOOST_PP_CAT(rewriting_rule_,__LINE__)

#define REWRITE(name,lhs,rhs) \
  static rewriting_rule REWRITING_NAME \
  (lhs, rhs, #name, pattern_cond_vect(), pattern_excl_vect())
#define REWRIT3(name,lhs,rhs,cond) \
  static rewriting_rule REWRITING_NAME \
  (lhs, rhs, #name, pattern_cond_vect() && cond, pattern_excl_vect())
#define REWRITe(name,lhs,rhs,excl) \
  static rewriting_rule REWRITING_NAME \
  (lhs, rhs, #name, pattern_cond_vect(), pattern_excl_vect() && excl)
#define REWRIT9(name,lhs,rhs,cond,excl) \
  static rewriting_rule REWRITING_NAME \
  (lhs, rhs, #name, pattern_cond_vect() && cond, pattern_excl_vect() && excl)

/*
Naming convention: operator name followed by
  x (expand term)      f (factor term)      m (mix)
  a (approximate expr) e (accurate expr)    i (irrelevant)
  l (left hand side)   r (right hand side)  b (both)
  s (absolute error)   q (relative error)
*/

// OPP

REWRITe(opp_mibs,
	-a - -b,
	-(a - b),
	a ^ b);

REWRIT9(opp_mibs,
	(-a - -b) / -b,
	(a - b) / b,
	~b,
	a ^ b);

// ADD

REWRITE(add_xals,
	b + c,
	hide((b - a) + (a + c)));

REWRITE(add_xars,
	c + b,
	hide((c + a) + (b - a)));

REWRITe(add_mibs,
	(a + b) - (c + d),
	hide((a - c) + (b - d)),
	a ^ c && b ^ d);

REWRITe(add_fils,
	(a + b) - (a + c),
	b - c,
	b ^ c);

REWRITe(add_firs,
	(a + b) - (c + b),
	a - c,
	a ^ c);

REWRIT9(add_filq,
	((a + b) - (a + c)) / (a + c),
	(b - c) / (a + c),
	~(a + c),
	b ^ c);

REWRIT9(add_firq,
	((a + b) - (c + b)) / (c + b),
	(a - c) / (c + b),
	~(c + b),
	a ^ c);

// SUB

REWRITe(sub_xals,
	b - c,
	hide((b - a) + (a - c)),
	a ^ c && b ^ c);

REWRITe(sub_xars,
	c - b,
	hide((c - a) - (b - a)),
	b ^ c); // no a^c so that the rule can be used to revert a-b

REWRITe(sub_mibs,
	(a - b) - (c - d),
	hide((a - c) - (b - d)),
	a ^ c && b ^ d);

REWRITe(sub_fils,
	(a - b) - (a - c),
	hide(-(b - c)),
	b ^ c);

REWRITe(sub_firs,
	(a - b) - (c - b),
	a - c,
	a ^ c);

REWRIT9(sub_filq,
	((a - b) - (a - c)) / (a - c),
	hide(-((b - c) / (a - c))),
	~(a - c),
	b ^ c);

REWRIT9(sub_firq,
	((a - b) - (c - b)) / (c - b),
	(a - c) / (c - b),
	~(c - b),
	a ^ c);

// MUL

REWRITE(mul_xals,
	b * c,
	hide(hide((b - a) * c) + a * c));

REWRITE(mul_xars,
	c * b,
	hide(hide(c * (b - a)) + c * a));

REWRITe(mul_fils,
	a * b - a * c,
	hide(a * (b - c)),
	b ^ c);

REWRITe(mul_firs,
	a * c - b * c,
	hide((a - b) * c),
	a ^ b);

REWRITe(mul_mars,
	a * b - c * d,
	hide(hide(a * (b - d)) + hide((a - c) * d)),
	a ^ c && b ^ d);

REWRITe(mul_mals,
	a * b - c * d,
	hide(hide((a - c) * b) + hide(c * (b - d))),
	a ^ c && b ^ d);

REWRITe(mul_mabs,
	a * b - c * d,
	hide(hide(hide(a * (b - d)) + hide((a - c) * b)) - hide((a - c) * (b - d))),
	a ^ c && b ^ d);

REWRITe(mul_mibs,
	a * b - c * d,
	hide(hide(hide(c * (b - d)) + hide((a - c) * d)) + hide((a - c) * (b - d))),
	a ^ c && b ^ d);

REWRITe(mul_filq,
	(a * b - a * c) / (a * c),
	(b - c) / c,
	b ^ c);

REWRITe(mul_firq,
	(a * b - c * b) / (c * b),
	(a - c) / c,
	a ^ c);

// DIV

REWRITe(div_firq,
	(a / b - c / b) / (c / b),
	(a - c) / c,
	a ^ c);

REWRIT9(div_xals,
	b / c,
	hide((b - a) / c + a / c),
	~c,
	a ^ c && b ^ c);

REWRIT3(div_fir,
	(a * b) / b,
	a,
	~b);

REWRIT3(div_fil,
	(a * b) / a,
	b,
	~a);

// SQRT

REWRIT9(sqrt_mibs,
	sqrt(a) - sqrt(b),
	hide((a - b) / hide(sqrt(a) + sqrt(b))),
	a >= 0 && b >= 0,
	a ^ b);

REWRIT9(sqrt_mibq,
	(sqrt(a) - sqrt(b)) / sqrt(b),
	hide(sqrt(hide(one + (a - b) / b)) - one),
	a >= 0 && b > 0,
	a ^ b);

// ERR

REWRITe(sub_xals, //actually err_xers
	c - a,
	hide((c - b) + (b - a)),
	a ^ c && b ^ c);

/* bad bad Zoot
REWRIT9(err_xabq,
	a / b,
	one + (a - b) / b,
	~b,
	a ^ b);
*/

/* ???
REWRIT9(err_fabq,
	one + (a - b) / b,
	a / b,
	~b,
	a ^ b);
*/

// VAL

REWRITE(val_xabs,
	b,
	hide(a + (b - a)));

REWRITE(val_xebs,
	a_b,
	hide(b - (b - a)));

REWRIT3(val_xabq,
	b,
	hide(a * hide(one + (b - a) / a)),
	~a);

REWRIT3(val_xebq,
	a_b,
	hide(b / hide(one + (b - a) / a)),
	~a && ~b);

// BLI

REWRIT3(square_sqrt,
	sqrt(a) * sqrt(a),
	a,
	a >= 0);

REWRIT3(addf_1,
	a / (a + b),
	hide(one / hide(one + b / a)),
	~a && ~(a + b));

REWRIT9(addf_2,
	a / (a + b),
	hide(one - b / (a + b)),
	~(a + b),
	a ^ b);

REWRIT9(addf_3,
	a / (a - b),
	hide(one / hide(one - b / a)),
	~a && ~(a - b),
	a ^ b);

REWRIT9(addf_4,
	a / (a - b),
	hide(one + b / (a - b)),
	~a && ~(a - b),
	a ^ b);

REWRIT9(addf_5,
	b / (a + b),
	hide(one / hide(a / b + one)),
	~b && ~(a + b),
	a ^ b);

REWRIT9(addf_6,
	b / (a + b),
	hide(one - a / (a + b)),
	~(a + b),
	a ^ b);

REWRIT9(addf_7,
	b / (a - b),
	hide(one / hide(a / b - one)),
	~b && ~(a - b),
	a ^ b);

REWRIT9(addf_8,
	b / (a - b),
	hide(a / (a - b) - one),
	~a && ~(a - b),
	a ^ b);
