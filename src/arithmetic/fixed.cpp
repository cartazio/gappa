/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <map>
#include <sstream>
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

struct fixed_format: gs_rounding {
  int min_exp;
  virtual int shift_val(int exp, int) const { return min_exp - exp; }
  fixed_format() {}
  fixed_format(int e): min_exp(e) {}
};

struct fixed_rounding_class: function_class
{
  fixed_format format;
  direction_type type;
  std::string ident;
  fixed_rounding_class(fixed_format const &f, direction_type t, std::string const &i)
    : function_class(UOP_ID, TH_RND | TH_ABS | (t == ROUND_ZR || t == ROUND_AW ? TH_ABS_EXA_BND | TH_ABS_APX_BND : 0)),
      format(f), type(t), ident(i) {}
  virtual interval round                         (interval const &, std::string &) const;
  virtual interval absolute_error                                  (std::string &) const;
  virtual interval absolute_error_from_exact_bnd (interval const &, std::string &) const;
  virtual interval absolute_error_from_approx_bnd(interval const &, std::string &) const;
  virtual std::string description() const { return "rounding_fixed" + ident; }
  virtual std::string pretty_name() const;
};

interval fixed_rounding_class::round(interval const &i, std::string &name) const {
  rounding_fun f = direction_functions[type];
  number a = round_number(lower(i), &format, f);
  number b = round_number(upper(i), &format, f);
  name = std::string("fixed_round,") + direction_names[type];
  return interval(a, b);
}

interval fixed_rounding_class::absolute_error(std::string &name) const {
  name = std::string("fixed_error,") + direction_names[type];
  if (rnd_to_nearest(type)) return from_exponent(format.min_exp - 1, 0);
  return from_exponent(format.min_exp, rnd_global_direction_abs(type));
}

interval fixed_rounding_class::absolute_error_from_exact_bnd(interval const &i, std::string &name) const {
  name = "fixed_error_dir";
  return from_exponent(format.min_exp, rnd_global_direction_abs(type, i, false));
}

interval fixed_rounding_class::absolute_error_from_approx_bnd(interval const &i, std::string &name) const {
  name = "fixed_error_inv";
  return from_exponent(format.min_exp, rnd_global_direction_abs(type, i, true));
}

std::string fixed_rounding_class::pretty_name() const
{
  std::ostringstream s;
  s << "fixed<" << format.min_exp << ',' << direction_names[type] << '>';
  return s.str();
}

struct fixed_rounding_generator: function_generator
{
  fixed_rounding_generator(): function_generator("fixed") {}
  static function_class const *generate(direction_type, int);
  virtual function_class const *operator()(function_params const &) const;
};

typedef std::map< int, fixed_rounding_class > fixed_cache;
static fixed_cache cache;

function_class const *fixed_rounding_generator::generate(direction_type d, int min_exp) {
  if (d == ROUND_ARGL) return NULL;
  int h = (min_exp << 8) | (int)d;
  fixed_cache::const_iterator i = cache.find(h);
  if (i != cache.end()) return &i->second;
  std::ostringstream s;
  s << ',' << direction_names[d] << ',' << min_exp;
  i = cache.insert(std::make_pair(h, fixed_rounding_class(fixed_format(min_exp), d, s.str()))).first;
  return &i->second;
}

function_class const *fixed_rounding_generator::operator()(function_params const &p) const {
  int min_exp;
  if (p.size() != 2 || !param_int(p[0], min_exp)) return NULL;
  return generate(get_direction(p[1]), min_exp);
}

static fixed_rounding_generator dummy;

struct int_rounding_generator: function_generator {
  int_rounding_generator(): function_generator("int") {}
  virtual function_class const *operator()(function_params const &) const;
};

function_class const *int_rounding_generator::operator()(function_params const &p) const {
  if (p.size() != 1) return NULL;
  return fixed_rounding_generator::generate(get_direction(p[0]), 0);
}

static int_rounding_generator dummy2;

// FIX_OF_FIXED
REGISTER_SCHEME_BEGIN(fix_of_fixed);
  fixed_rounding_class const *rnd;
  fix_of_fixed_scheme(predicated_real const &r, fixed_rounding_class const *f)
    : proof_scheme(r, preal_vect()), rnd(f) {}
REGISTER_SCHEME_END_PREDICATE(fix_of_fixed);

node *fix_of_fixed_scheme::generate_proof(property const []) const
{
  return create_theorem(0, NULL, property(real, rnd->format.min_exp), "fix_of_fixed");
}

proof_scheme *fix_of_fixed_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  fixed_rounding_class const *f = dynamic_cast< fixed_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new fix_of_fixed_scheme(real, f);
}

// FIXED_OF_FIX
REGISTER_SCHEME_BEGIN(fixed_of_fix);
  long min_exp;
  fixed_of_fix_scheme(predicated_real const &r, predicated_real const &v, long e)
    : proof_scheme(r, preal_vect(1, v)), min_exp(e) {}
REGISTER_SCHEME_END_PATTERN(fixed_of_fix, predicated_real(pattern(0), pattern(1), PRED_EQL));

node *fixed_of_fix_scheme::generate_proof(property const hyps[]) const
{
  if (hyps[0].cst() < min_exp) return NULL;
  return create_theorem(1, hyps, property(real), "fixed_of_fix");
}

proof_scheme *fixed_of_fix_scheme::factory(predicated_real const &real, ast_real_vect const &holders)
{
  ast_real const *r = holders[1];
  real_op const *o = boost::get<real_op const>(holders[0]);
  if (!o || !o->fun || o->fun->type != UOP_ID || r != o->ops[0])
    return NULL;
  fixed_rounding_class const *f = dynamic_cast<fixed_rounding_class const *>(o->fun);
  if (!f) return NULL;
  return new fixed_of_fix_scheme(real, predicated_real(r, PRED_FIX), f->format.min_exp);
}

// FIXED_OF_FIX_REDUCED
REGISTER_SCHEME_BEGIN(fixed_of_fix_reduced);
  fixed_rounding_class const *rnd;
  fixed_of_fix_reduced_scheme(ast_real const *r, predicated_real const &v, fixed_rounding_class const *f)
    : proof_scheme(predicated_real(r, PRED_BND), preal_vect(1, v)), rnd(f) {}
REGISTER_SCHEME_END(fixed_of_fix_reduced);

node *fixed_of_fix_reduced_scheme::generate_proof(property const hyps[]) const
{
  property const &hyp = hyps[0];
  long weight = hyp.cst();
  if (weight >= rnd->format.min_exp) return NULL;
  if (rnd_to_nearest(rnd->type)) return NULL;
  int dir = rnd_global_direction_abs(rnd->type);
  interval error = from_exponent(rnd->format.min_exp, dir);
  number adj = upper(from_exponent(weight, 1));
  interval adjust(adj, adj);
  if (dir <= 0) error = intersect(error, error + adjust);
  if (dir >= 0) error = intersect(error, error - adjust);
  return create_theorem(1, &hyp, property(real, error), "fixed_of_fix_reduced");
}

proof_scheme *fixed_of_fix_reduced_scheme::factory(ast_real const *real)
{
  if (is_unknown_theorem("fixed_of_fix_reduced")) return NULL;
  ast_real const *holders[2];
  fixed_rounding_class const *f = dynamic_cast< fixed_rounding_class const * >(absolute_rounding_error(real, holders));
  if (!f) return NULL;
  return new fixed_of_fix_reduced_scheme(real, predicated_real(holders[0], PRED_FIX), f);
}

// BND_OF_BND_FIX
REGISTER_SCHEME_BEGIN(bnd_of_bnd_fix);
  bnd_of_bnd_fix_scheme(preal_vect const &v): proof_scheme(v[0], v) {}
REGISTER_SCHEME_END(bnd_of_bnd_fix);

node *bnd_of_bnd_fix_scheme::generate_proof(property const hyps[]) const
{
  fixed_format format(hyps[1].cst());
  interval const &i = hyps[0].bnd();
  number a = round_number(lower(i), &format, &fixed_format::roundUP);
  number b = round_number(upper(i), &format, &fixed_format::roundDN);
  property res(real, interval(a, (a <= b) ? b : a));
  return create_theorem(2, hyps, res, "bnd_of_bnd_fix");
}

extern bool is_hidden(ast_real const *);

proof_scheme *bnd_of_bnd_fix_scheme::factory(ast_real const *real)
{
  if (is_hidden(real) || is_constant(real)) return NULL;
  real_op const *p = boost::get< real_op const >(real);
  if (p && (p->type == UOP_ABS || p->type == UOP_SQRT || p->type == BOP_DIV)) return NULL;
  preal_vect hyps;
  hyps.push_back(predicated_real(real, PRED_BND));
  hyps.push_back(predicated_real(real, PRED_FIX));
  return new bnd_of_bnd_fix_scheme(hyps);
}

// FIX_FIXED_OF_FIX

REGISTER_SCHEME_BEGIN(fix_fixed_of_fix);
  fix_fixed_of_fix_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r, preal_vect(1, n)) {}
REGISTER_SCHEME_END_PREDICATE(fix_fixed_of_fix);

node *fix_fixed_of_fix_scheme::generate_proof(property const hyps[]) const
{
  return create_theorem(1, hyps, property(real, hyps[0].cst()), "fix_fixed_of_fix");
}

proof_scheme *fix_fixed_of_fix_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FIX) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  fixed_rounding_class const *f = dynamic_cast< fixed_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new fix_fixed_of_fix_scheme(real, predicated_real(r->ops[0], PRED_FIX));
}

// FLT_FIXED_OF_FLT

REGISTER_SCHEME_BEGIN(flt_fixed_of_flt);
  flt_fixed_of_flt_scheme(predicated_real const &r, predicated_real const &n)
    : proof_scheme(r, preal_vect(1, n)) {}
REGISTER_SCHEME_END_PREDICATE(flt_fixed_of_flt);

node *flt_fixed_of_flt_scheme::generate_proof(property const hyps[]) const
{
  return create_theorem(1, hyps, property(real, hyps[0].cst()), "flt_fixed_of_flt");
}

proof_scheme *flt_fixed_of_flt_scheme::factory(predicated_real const &real) {
  if (real.pred() != PRED_FLT) return NULL;
  real_op const *r = boost::get< real_op const >(real.real());
  if (!r) return NULL;
  fixed_rounding_class const *f = dynamic_cast< fixed_rounding_class const * >(r->fun);
  if (!f) return NULL;
  return new flt_fixed_of_flt_scheme(real, predicated_real(r->ops[0], PRED_FLT));
}
