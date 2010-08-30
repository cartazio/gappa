/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cassert>
#include <cstdlib>
#include <iostream>
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"

#define GAPPADEF "Gappa.Gappa_definitions."
#define COQRDEF "Reals.Rdefinitions."

static char const *theorem_defs[][2] = {
  { "subset", "$gpred_bnd.$t $x $1i $i $" },
  { "subset_l", "$gpred_bnd.$t $x $1i $l $" },
  { "subset_r", "$gpred_bnd.$t $x $1i $u $" },
  { "abs_subset", "$gpred_abs.$t $x $1i $i $" },
  { "rel_subset", "$gpred_rel.$t $x $y $1i $i $" },
  { "fix_subset", "$gpred_fixflt.$t $x $1c $c $" },
  { "flt_subset", "$gpred_fixflt.$t $x $1c $c $" },

  { "intersect", "$gpred_bnd.$t $x $1i $2i $i $" },
  { "intersect_hb", "$gpred_bnd.$t $x $1u $2i $i $" },
  { "intersect_bh", "$gpred_bnd.$t $x $2l $1i $i $" },
  { "intersect_aa", "$gpred_abs.$t $x $1i $2i $i $" },
  { "intersect_rr", "$gpred_rel.$t $x $y $1i $2i $i $" },
  { "intersect_rr0", "$gpred_rel.$t $1x $1y $1i $2i $i $" },
  { "absurd_intersect", "$gpred_bnd.$t $1x $1i $2i $" },
  { "absurd_intersect_hb", "$gpred_bnd.$t $1x $1u $2i $" },
  { "absurd_intersect_bh", "$gpred_bnd.$t $1x $1i $2l $" },
  { "absurd_intersect_aa", "$gpred_abs.$t $1x $1i $2i $" },

  { "bnd_of_abs", "$gpred_abs.$t $1x $1i $i $" },
  { "abs_of_bnd_p", "$gpred_abs.$t $1x $1i $i $" },
  { "abs_of_bnd_o", "$gpred_abs.$t $1x $1i $i $" },
  { "abs_of_bnd_n", "$gpred_abs.$t $1x $1i $i $" },
  { "abs_of_uabs", "$gpred_abs.$t $x $1i $" },
  { "uabs_of_abs", "$gpred_abs.$t $1x $i $1p" },
  { "bnd_of_bnd_abs_p", "$gpred_abs.$t $1x $1i $2i $i $" },
  { "bnd_of_bnd_abs_n", "$gpred_abs.$t $1x $1i $2i $i $" },

  { "constant1", "$gpred_bnd.$t _ $i $" },
  { "constant2", "$gpred_bnd.$t _ $i $" },
  { "constant10", "$gpred_bnd.$t _ $i $" },

  { "neg", "$gpred_bnd.$t $1x $1i $i $" },
  { "add", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "sub", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_pp", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_po", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_pn", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_op", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_oo", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_on", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_np", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_no", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "mul_nn", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_pp", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_pn", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_op", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_on", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_np", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "div_nn", "$gpred_bnd.$t $1x $2x $1i $2i $i $" },
  { "square_p", "$gpred_bnd.$t $1x $1i $i $" },
  { "square_o", "$gpred_bnd.$t $1x $1i $i $" },
  { "square_n", "$gpred_bnd.$t $1x $1i $i $" },
  { "sqrt", "$gpred_bnd.sqrtG $1x $1i $i $" },

  { "sub_refl", "$gpred_bnd.$t _ $i $" },
  { "div_refl", "$gpred_bnd.$t $1x $i $" },

  { "add_aa_p", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "add_aa_o", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "add_aa_n", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_p", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_o", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_n", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "mul_aa", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "div_aa", "$gpred_abs.$t $1x $2x $1i $2i $i $" },

  { "mul_rr", "$gpred_rel.$t $1x $1y $2x $2y $1i $2i $i $" },
  { "div_rr", "$gpred_rel.$t $1x $1y $2x $3x $1i $2i $i $" },
  { "compose", "$gpred_rel.$t $1x $1y $2y $1i $2i $i $" },

  { "add_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "sub_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "mul_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "mul_flt", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },

  { "nzr_of_abs", "$gpred_nzr.$t $x $1i $" },
  { "nzr_of_bnd_p", "$gpred_nzr.$t $x $1i $" },
  { "nzr_of_bnd_n", "$gpred_nzr.$t $x $1i $" },
  { "nzr_of_nzr_rel", "$gpred_nzr.$t $x $1x $2i $" },
  { "nzr_of_nzr_rel_rev", "$gpred_nzr.$t $1x $x $2i $" },

  { "bnd_of_nzr_rel", "$gpred_rel.$t $2x $1x $i $1p $2p" },
  { "rel_of_nzr_bnd", "$gpred_rel.$t $x $1x $2i $1p $2p" },
  { "rel_of_equal", "$gpred_rel.$t $x $y $1i $i $" },
  { "error_of_rel_pp", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_po", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_pn", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_op", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_oo", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_on", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_np", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_no", "$gpred_rel.$t $1x $2x $1i $2i $i $" },
  { "error_of_rel_nn", "$gpred_rel.$t $1x $2x $1i $2i $i $" },

  { "fix_of_singleton_bnd", "$gpred_fixflt.$t $x $1i $c $" },
  { "flt_of_singleton_bnd", "$gpred_fixflt.$t $x $1i $c $" },
  { "fix_of_flt_bnd", "$gpred_fixflt.$t $1x $2i $c $1c $" },
  { "flt_of_fix_bnd", "$gpred_fixflt.$t $1x $2i $1c $c $" },

  { "fix_of_float", "$gfloat.$t _ _ _ _ $c $" },
  { "flt_of_float", "$gfloat.$t _ _ _ $c _ $" },
  { "float_of_fix_flt", "$gfloat.$t _ $1x $i $1c _ $2c _ $" },

  { "float_round", "$gfloat.$t _ _ _ $1x $1i $i $" },
  { "float_enforce", "$gfloat.$t _ _ _ _ $1i $i $" },
  { "float_absolute_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_absolute_wide_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_relative_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "rel_of_fix_float_ne", "$gfloat.$t _ _ $1c $1x $i $" },

  { "fix_of_fixed", "$gfixed.$t _ _ _ $c $" },
  { "fixed_of_fix", "$gfixed.$t _ $1x $1c _ $i $" },
  { "bnd_of_bnd_fix", "$gfixed.$t $1x $2c $1i $i $" },

  { "fixed_round", "$gfixed.$t _ _ $1x $1i $i $" },
  { "fixed_error_dn", "$gfixed.$t _ _ $i $" },

  { "opp_mibs", "$grewriting.$t _ _ $i $1p" },
  { "add_xals", "$grewriting.$t _ _ _ $i $1p" },
  { "add_xars", "$grewriting.$t _ _ _ $i $1p" },
  { "sub_xals", "$grewriting.$t _ _ _ $i $1p" },
  { "sub_xars", "$grewriting.$t _ _ _ $i $1p" },
  { "mul_xals", "$grewriting.$t _ _ _ $i $1p" },
  { "mul_xars", "$grewriting.$t _ _ _ $i $1p" },
  { "add_mibs", "$grewriting.$t _ _ _ _ $i $1p" },
  { "add_fils", "$grewriting.$t _ _ _ $i $1p" },
  { "add_firs", "$grewriting.$t _ _ _ $i $1p" },
  { "add_filq", "$grewriting.$t _ _ _ $i $1p $2p" },
  { "add_firq", "$grewriting.$t _ _ _ $i $1p $2p" },
  { "sub_mibs", "$grewriting.$t _ _ _ _ $i $1p" },
  { "sub_fils", "$grewriting.$t _ _ _ $i $1p" },
  { "sub_firs", "$grewriting.$t _ _ _ $i $1p" },
  { "sub_filq", "$grewriting.$t _ _ _ $i $1p $2p" },
  { "sub_firq", "$grewriting.$t _ _ _ $i $1p $2p" },
  { "mul_fils", "$grewriting.$t _ _ _ $i $1p" },
  { "mul_firs", "$grewriting.$t _ _ _ $i $1p" },
  { "mul_mals", "$grewriting.$t _ _ _ _ $i $1p" },
  { "mul_mars", "$grewriting.$t _ _ _ _ $i $1p" },
  { "mul_mabs", "$grewriting.$t _ _ _ _ $i $1p" },
  { "mul_mibs", "$grewriting.$t _ _ _ _ $i $1p" },
  { "err_xalq", "$grewriting.$t _ $2x $3x $i $1p $2p $3p" },
  { "mul_filq", "$grewriting.$t _ $1x $1y $i $1p" },
  { "mul_firq", "$grewriting.$t $1x _ $1y $i $1p" },
  { "sqrt_mibs", "$grewriting.$t $1x $2x $1i $2i $3i $" },
  { "sqrt_mibq", "$grewriting.$t $1x $2x $1i $2i $3i $" },
  { "val_xebs", "$grewriting.$t $x _ $i $1p" },
  { "val_xabs", "$grewriting.$t _ $x $i $1p" },
  { "val_xebq", "$grewriting.$t $x $2x $i $1p $2p $3p" },
  { "val_xabq", "$grewriting.$t $1x $x $i $1p $2p" },
  { "div_mibq", "$grewriting.$t _ $1x $2x $3x $i $1p $2p $3p $4p" },
  { "div_xals", "$grewriting.$t _ _ $1x $i $1p $2p" },
  { "div_firq", "$grewriting.$t $1x _ $1y $i $1p" },
  { "div_fil", "$grewriting.$t $2x $1x $i $1p $2p" },
  { "div_fir", "$grewriting.$t $1x $2x $i $1p $2p" },
  { "err_xabq", "$grewriting.$t _ $1x $i $1p $2p" },
  { "err_fabq", "$grewriting.$t _ $1x $i $1p $2p" },
  { "addf_1", "$grewriting.$t $1x _ $i $1p $2p $3p" },
  { "addf_2", "$grewriting.$t _ _ $i $1p $2p" },
  { "addf_3", "$grewriting.$t $1x _ $i $1p $2p $3p" },
  { "addf_4", "$grewriting.$t _ _ $i $1p $2p" },
  { "addf_5", "$grewriting.$t _ $1x $i $1p $2p $3p" },
  { "addf_6", "$grewriting.$t _ _ $i $1p $2p" },
  { "addf_7", "$grewriting.$t _ $1x $i $1p $2p $3p" },
  { "addf_8", "$grewriting.$t _ _ $i $1p $2p" },

  { NULL, NULL }
};

struct theorem_map : std::map<std::string, char const *>
{
  theorem_map()
  {
    for (char const *(*p)[2] = theorem_defs; (*p)[0]; ++p) {
      insert(std::pair<std::string, char const *>((*p)[0], (*p)[1]));
    }
  }
};

theorem_map theorems;

std::ostream *out_vars;

extern std::string get_real_split(number const &f, int &exp, bool &zero);

static std::string convert_name(std::string const &name)
{
  std::string::size_type p2 = name.find(',');
  if (p2 == std::string::npos) return name;
  std::string prefix = name.substr(0, p2);
  bool rounding = prefix == "rounding_fixed" || prefix == "rounding_float";
  bool fragile = false;
  std::ostringstream res;
  if (rounding) res << "Gappa.Gappa_" << prefix.substr(9) << '.';
  res << prefix;
  do {
    std::string::size_type p1 = p2 + 1;
    p2 = name.find(',', p1);
    std::string s(name, p1, p2 == std::string::npos ? p2 : p2 - p1);
    if (!std::isalpha(s[0])) {
      res << " (" << s << ')';
      fragile = true;
    } else if (rounding && s.length() == 2) {
      res << " Gappa.Gappa_round_def.round"
          << (char)std::toupper(s[0]) << (char)std::toupper(s[1]);
      fragile = true;
    } else res << '_' << s;
  } while (p2 != std::string::npos);
  if (!fragile) return res.str();
  return '(' + res.str() + ')';
}

static id_cache< std::string > displayed_floats;

static std::string display(number const &f)
{
  std::ostringstream s;
  bool zero;
  int exp;
  s << '(' << get_real_split(f, exp, zero);
  s << ") (" << (zero ? 0 : exp) << ')';
  std::string const &s_ = s.str();
  int f_id = displayed_floats.find(s_);
  std::string name = composite('f', f_id);
  if (f_id >= 0)
    *out << "let " << name << " := " GAPPADEF "Float2 " << s_ << " in\n";
  return name;
}

static id_cache< std::string > displayed_intervals;

static std::string display(interval const &i)
{
  std::ostringstream s;
  s << display(lower(i)) << ' ' << display(upper(i));
  std::string const &s_ = s.str();
  int i_id = displayed_intervals.find(s_);
  std::string name = composite('i', i_id);
  if (i_id >= 0)
    *out << "let " << name << " := " GAPPADEF "makepairF " << s_ << " in\n";
  return name;
}

static id_cache< ast_real const * > displayed_reals;

static std::string display(ast_real const *r)
{
  if (hidden_real const *h = boost::get< hidden_real const >(r))
    r = h->real;
  int r_id = displayed_reals.find(r);
  std::string name = r->name ? '_' + r->name->name : composite('r', r_id);
  if (r_id < 0)
    return name;
  if (boost::get< undefined_real const >(r)) {
    *out_vars << '(' << name << " : " COQRDEF "R) ";
    return name;
  }
  auto_flush plouf;
  plouf << "let " << name << " := ";
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r))
  {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0) plouf << "Gappa.Gappa_pred_bnd.Float1 0";
    else if (n.exponent == 0) plouf << "Gappa.Gappa_pred_bnd.Float1 (" << m << ')';
    else plouf << GAPPADEF "Float" << n.base << " (" << m << ") (" << n.exponent << ')';
  }
  else if (real_op const *o = boost::get< real_op const >(r))
  {
    if (o->type == ROP_FUN)
    {
      std::string description = o->fun->description();
      plouf << convert_name(description) << ' ' << display(o->ops[0]);
      for (ast_real_vect::const_iterator i = ++(o->ops.begin()),
           end = o->ops.end(); i != end; ++i)
        plouf << ' ' << display(*i);
    }
    else
    {
      char const *s;
      switch (o->type) {
      case BOP_ADD: s = COQRDEF "Rplus"; break;
      case BOP_SUB: s = COQRDEF "Rminus"; break;
      case BOP_MUL: s = COQRDEF "Rmult"; break;
      case BOP_DIV: s = COQRDEF "Rdiv"; break;
      case UOP_ABS: s = "Reals.Rbasic_fun.Rabs"; break;
      case UOP_SQRT: s = "Reals.R_sqrt.sqrt"; break;
      case UOP_NEG: s = COQRDEF "Ropp"; break;
      default: assert(false);
      }
      plouf << s << ' ' << display(o->ops[0]);
      if (o->ops.size() == 2) plouf << ' ' << display(o->ops[1]);
    }
  }
  else
    assert(false);
  plouf << " in\n";
  return name;
}

static id_cache< std::string > displayed_properties;

static std::string display(property const &p)
{
  std::ostringstream s;
  predicate_type t = p.real.pred();
  ast_real const *real = p.real.real();
  if (p.null())
  {
    return GAPPADEF "contradiction";
  }
  else if (p.real.pred_bnd())
  {
    interval const &bnd = p.bnd();
    if (lower(bnd) == number::neg_inf) {
      assert(t == PRED_BND);
      s << COQRDEF "Rle " << display(real) << ' ' << display(upper(bnd));
    } else if (upper(bnd) == number::pos_inf) {
      assert(t == PRED_BND);
      s << COQRDEF "Rle " << display(lower(bnd)) << ' ' << display(real);
    }
    else
    {
      switch (t) {
      case PRED_BND:
        s << GAPPADEF "BND " << display(real) << ' ' << display(bnd);
        break;
      case PRED_ABS:
        s << GAPPADEF "ABS " << display(real) << ' ' << display(bnd);
        break;
      case PRED_REL:
        s << GAPPADEF "REL " << display(real) << ' ' << display(p.real.real2())
          << ' ' << display(bnd);
        break;
      default:
        assert(false);
      }
    }
  }
  else
  {
    switch (t) {
    case PRED_FIX:
      s << GAPPADEF "FIX " << display(real) << " (" << p.cst() << ')';
      break;
    case PRED_FLT:
      s << GAPPADEF "FLT " << display(real) << " (" << p.cst() << ')';
      break;
    case PRED_NZR:
      s << GAPPADEF "NZR " << display(real);
      break;
    default:
      assert(false);
    }
  }
  std::string s_ = s.str();
  int p_id = displayed_properties.find(s_);
  std::string name = composite('p', p_id);
  if (p_id >= 0)
    *out << "let " << name << " := " << s_ << " in (* " << dump_property(p) << " *)\n";
  return name;
}

typedef std::map< predicated_real, std::pair< int, property const * > > property_map;

static void apply_theorem(auto_flush &plouf, std::string const &th,
                          property const &res, property const *hyp,
                          property_map const *pmap = NULL, int *num = NULL)
{
  theorem_map::const_iterator it = theorems.find(th);
  if (it == theorems.end()) {
    std::cerr << "Theorem '" << th
              << "' is missing from the coq-lambda back-end. Aborting.\n";
    exit(1);
  }
  std::ostringstream s;
  char const *p = it->second;
  bool has_comp = false;
  int max = 0;
  std::string buf;
  for (; *p; ++p)
  {
    if (*p != '$') { s << *p; continue; }
    ++p;
    property const *h = &res;
    if (*p >= '1' && *p <= '9')
    {
      int n = *(p++) - '1';
      h = &hyp[n];
      for (; max <= n; ++max) {
        char t[] = { ' ', '$', '1' + max, 'p', '\0' };
        buf += t;
      }
    }
    switch (*p) {
      case 'g': s << "Gappa.Gappa_"; break;
      case 't': s << th; break;
      case 'i': s << display(h->bnd()); break;
      case 'l': s << display(lower(h->bnd())); break;
      case 'u': s << display(upper(h->bnd())); break;
      case 'c': s << '(' << h->cst() << ')'; break;
      case 'x': s << display(h->real.real()); break;
      case 'y': s << display(h->real.real2()); break;
      case '\0':
        has_comp = true;
        p = buf.c_str();
        break;
      case 'p':
        s << 'h';
        if (pmap) {
          property_map::const_iterator pki = pmap->find(h->real);
          assert(pki != pmap->end());
          s << pki->second.first;
        } else if (num)
          s << num[h - hyp];
        else
           s << h - hyp;
        break;
      case 'b':
        has_comp = true;
        break;
      default:
        s << '$';
    }
  }
  if (!has_comp)
    plouf << s.str();
  else
    plouf << '(' << s.str() << " _)";
}

static std::string display(node *n);

static std::string display(theorem_node *t)
{
  static int t_id = 0;
  std::string name = composite('t', ++t_id);
  auto_flush plouf;
  plouf << "let " << name;
  int num_hyp = 0;
  for (property_vect::const_iterator i = t->hyp.begin(),
       i_end = t->hyp.end(); i != i_end; ++i)
  {
    plouf << " (h" << num_hyp++ << " : " << display(*i) << ')';
  }
  plouf << " : " <<  display(t->res) << " := ";
  apply_theorem(plouf, convert_name(t->name), t->res, &*t->hyp.begin());
  plouf << " in\n";
  return name;
}

static void invoke_lemma(auto_flush &plouf, property_vect const &hyp, property_map const &pmap)
{
  for (property_vect::const_iterator j = hyp.begin(),
       j_end = hyp.end(); j != j_end; ++j)
  {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    predicate_type t = j->real.pred();
    if (j->real.pred_bnd())
    {
      interval const &i = pki->second.second->bnd(), &ii = j->bnd();
      assert(i <= ii);
      if (ii <= i)
        plouf << " h" << h;
      else
      {
        char const *prefix = "", *suffix = "";
        switch (t)
        {
          case PRED_ABS: prefix = "abs_"; break;
          case PRED_REL: prefix = "rel_"; break;
          case PRED_BND:
            if (lower(ii) == number::neg_inf)
              suffix = "_r";
            else if (upper(ii) == number::pos_inf)
              suffix = "_l";
            break;
          default: assert(false);
        }
        plouf << ' ';
        apply_theorem(plouf, std::string(prefix) + "subset" + suffix,
                      *j, pki->second.second, &pmap);
      }
    }
    else if (j->real.pred_cst())
    {
      long c = pki->second.second->cst(), cc = j->cst();
      assert((t == PRED_FIX && c >= cc) || (t == PRED_FLT && c <= cc));
      if (c == cc)
        plouf << " h" << h;
      else
      {
        char const *prefix = "";
        switch (t)
        {
          case PRED_FIX: prefix = "fix_"; break;
          case PRED_FLT: prefix = "flt_"; break;
          default: assert(false);
        }
        plouf << ' ';
        apply_theorem(plouf, std::string(prefix) + "subset",
                      *j, pki->second.second, &pmap);
      }
    }
    else
    {
      assert(t == PRED_NZR);
      plouf << " h" << h;
    }
  }
}

static void invoke_lemma(auto_flush &plouf, node *n, property_map const &pmap)
{
  if (n->type != HYPOTHESIS) {
    plouf << display(n);
    invoke_lemma(plouf, n->graph->get_hypotheses(), pmap);
  } else {
    property_vect hyp;
    hyp.push_back(n->get_result());
    invoke_lemma(plouf, hyp, pmap);
  }
}

static id_cache< node * > displayed_nodes;

static std::string display(node *n)
{
  assert(n);
  int n_id = displayed_nodes.find(n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  plouf << "let " << name;
  property_vect const &n_hyp = n->graph->get_hypotheses();
  property_map pmap;
  int num_hyp = 0;
  for (property_vect::const_iterator i = n_hyp.begin(),
       i_end = n_hyp.end(); i != i_end; ++i)
  {
    property const &p = *i;
    pmap[p.real] = std::make_pair(num_hyp++, &p);
  }
  node_vect const &pred = n->get_subproofs();
  property const &n_res = n->get_result();
  std::string p_res, prefix;
  if (n_res.null()) {
    p_res = GAPPADEF "contradiction";
    prefix = "absurd_";
  } else
    p_res = display(n_res);
  plouf << " : " << p_res << " := (* "
        << (!n_res.null() ? dump_property(n_res) : "contradiction") << " *)\n";
  switch (n->type) {
  case MODUS: {
    for (node_vect::const_iterator i = pred.begin(),
         i_end = pred.end(); i != i_end; ++i)
    {
      node *m = *i;
      property const &res = m->get_result();
      plouf << "  let h" << num_hyp << " : " << display(res) << " := "
            << display(m) << " in\n";
      pmap[res.real] = std::make_pair(num_hyp++, &res);
    }
    modus_node *mn = dynamic_cast< modus_node * >(n);
    assert(mn && mn->target);
    plouf << "  " << display(mn->target);
    invoke_lemma(plouf, mn->target->hyp, pmap);
    plouf << " in\n";
    break; }
  case INTERSECTION: {
    property hyps[2];
    int num[2];
    char const *suffix = "";
    for (int i = 0; i < 2; ++i)
    {
      node *m = pred[i];
      property const &res = m->get_result();
      hyps[i] = res;
      switch (res.real.pred()) {
        case PRED_BND:
          if (!is_bounded(res.bnd())) suffix = (i == 0) ? "_hb" : "_bh";
          break;
        case PRED_ABS:
          suffix = "_aa";
          break;
        case PRED_REL:
          suffix = res.real == n_res.real ? "_rr" : "_rr0";
          break;
        default:
          assert(false);
      }
      if (m->type == HYPOTHESIS) {
        property_map::iterator pki = pmap.find(res.real);
        assert(pki != pmap.end());
        num[i] = pki->second.first;
        continue;
      }
      plouf << "  let h" << num_hyp << " : " << display(res) << " := ";
      invoke_lemma(plouf, m, pmap);
      plouf << " in\n";
      num[i] = num_hyp++;
    }
    plouf << "  ";
    apply_theorem(plouf, std::string(prefix) + "intersect" + suffix,
                  n_res, hyps, NULL, num);
    plouf << " in\n";
    break; }
#if 0
  case UNION: {
    assert(pred.size() >= 2);
    node *mcase = pred[0];
    property const &pcase = mcase->get_result();
    assert(pcase.real.pred() == PRED_BND);
    property_map::mapped_type &hcase = pmap[pcase.real];
    if (mcase->type != HYPOTHESIS) {
      plouf << " assert (h" << num_hyp << " : " << display(pcase) << ").";
      invoke_lemma(plouf, mcase, pmap);
      hcase = std::make_pair(num_hyp, &pcase);
    }
    plouf << " generalize h" << hcase.first << ". clear h" << hcase.first << ".\n";
    for(node_vect::const_iterator i = pred.begin() + 1, i_end = pred.end(); i != i_end; ++i) {
      node *m = *i;
      property_vect const &m_hyp = m->graph->get_hypotheses();
      hcase.second = &m_hyp[0];
      plouf << " assert (u : " << display(m_hyp[0]) << " -> " << p_res << ")."
               " intro h" << hcase.first << ". (* " << m_hyp[0].bnd() << " *)\n";
      property const &res = m->get_result();
      interval const &mb = res.bnd(), &nb = n_res.bnd();
      if (!res.null()) { // not a contradictory result
        assert(mb <= nb);
        if (!(nb <= mb))
          plouf << " apply subset with " << display(mb) << ". 2: finalize.\n";
      }
      invoke_lemma(plouf, m, pmap);
      if (i + 1 != i_end)
        plouf << " next_interval (union) u.\n";
      else
        plouf << " exact u.\n";
    }
    plouf << "Qed.\n";
    break; }
#endif
  case GOAL: {
    node *m = pred[0];
    interval const &mb = m->get_result().bnd(), &nb = n_res.bnd();
    if (!(nb <= mb))
    {
      property const &res = m->get_result();
      plouf << "  let h" << num_hyp << " : " << display(res) << " := "
        << display(m) << " in ";
      pmap[res.real] = std::make_pair(num_hyp++, &res);
      char const *prefix = "", *suffix = "";
      if (m->get_result().real.pred() == PRED_REL) prefix = "rel_";
      if (lower(nb) == number::neg_inf) suffix = "_r";
      else if (upper(nb) == number::pos_inf) suffix = "_l";
      apply_theorem(plouf, prefix + std::string("subset") + suffix,
                    n_res, &res, &pmap);
    }
    else
    {
      plouf << "  " << display(m);
    }
    plouf << " in\n";
    break; }
  default:
    assert(false);
  }
  return name;
}

struct coq_lambda_backend: backend
{
  coq_lambda_backend(): backend("coq-lambda") {}
  void initialize(std::ostream &o) { out = &o; }
  void finalize() {}
  void reset() { displayed_nodes.clear(); }
  virtual std::string rewrite(ast_real const *, ast_real const *, pattern_cond_vect const &);
  virtual std::string theorem(node *n);
};

std::string coq_lambda_backend::rewrite
  (ast_real const *, ast_real const *, pattern_cond_vect const &)
{
  std::cerr << "Rewriting rules are not supported by the coq-lambda back-end.\n";
  exit(1);
  return "";
}

std::string coq_lambda_backend::theorem(node *n)
{
  int nb_hyps = n->graph->get_hypotheses().size();
  if (n->type == GOAL && n->get_subproofs()[0]->type == HYPOTHESIS) nb_hyps = 1;
  *out << "(* " << nb_hyps;
  if (n->get_result().null()) *out << ",contradiction";
  *out << " *)\n(fun ";
  std::ostringstream buf1, buf2, buf3;
  out_vars = out;
  out = &buf1;
  property_vect const &n_hyp = n->graph->get_hypotheses();
  int num_hyp = 0;
  for (property_vect::const_iterator i = n_hyp.begin(),
       i_end = n_hyp.end(); i != i_end; ++i)
  {
    buf3 << " (h" << num_hyp << " : " << display(*i) << ")";
    ++num_hyp;
  }
  out = &buf2;
  std::string s = display(n);
  out = out_vars;
  *out << "=>\n" << buf1.str();
  if (num_hyp) *out << "fun" << buf3.str() << " =>\n";
  *out << buf2.str() << s << ")\n";
  return s;
}

static struct coq_lambda_backend dummy;
