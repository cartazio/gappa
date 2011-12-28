/*
   Copyright (C) 2004 - 2012 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cassert>
#include <cstring>
#include <iostream>
#include <sstream>
#include "backends/backend.hpp"
#include "backends/coq_common.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "utils.hpp"

#define GAPPADEF "Gappa.Gappa_definitions."
#define COQRDEF "Reals.Rdefinitions."
#define FLOCQDEF "Flocq.Core.Fcore_"

extern std::string get_real_split(number const &f, int &exp, bool &zero);

namespace coq {

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
  { "sub_of_eql", "$gpred_bnd.$t $1x $1y $i $" },
  { "eql_of_cst", "$gpred_bnd.$t $1x $2x $1i $2i $" },

  { "neg_a", "$gpred_abs.$t $1x $i $1p" },
  { "add_aa_p", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "add_aa_o", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "add_aa_n", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_p", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_o", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "sub_aa_n", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "mul_aa", "$gpred_abs.$t $1x $2x $1i $2i $i $" },
  { "div_aa", "$gpred_abs.$t $1x $2x $1i $2i $i $" },

  { "add_rr", "$gpred_rel.$t $1x $1y $2x $2y $1i $2i $3i $i $1p $2p $3p $4p $b" },
  { "sub_rr", "$gpred_rel.$t $1x $1y $2x $2y $1i $2i $3i $i $1p $2p $3p $4p $b" },
  { "mul_rr", "$gpred_rel.$t $1x $1y $2x $2y $1i $2i $i $" },
  { "div_rr", "$gpred_rel.$t $1x $1y $2x $3x $1i $2i $i $" },
  { "compose", "$gpred_rel.$t $1x $1y $2y $1i $2i $i $" },
  { "compose_swap", "$gpred_rel.$t $1x $y $2x $3x $1i $2i $i $" },
  { "bnd_div_of_rel_bnd_div", "$gpred_rel.$t $1x $1y $3x $1i $2i $i $" },

  { "add_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "sub_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "mul_fix", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "mul_flt", "$gpred_fixflt.$t $1x $2x $1c $2c $c $" },
  { "sub_flt", "$gpred_fixflt.$t $1x $2x $1c $2c $3i $c $" },
  { "sub_flt_rev", "$gpred_fixflt.$t $1x $2x $1c $2c $3i $c $" },

  { "nzr_of_abs", "$gpred_nzr.$t $x $1i $" },
  { "nzr_of_bnd_p", "$gpred_nzr.$t $x $1i $" },
  { "nzr_of_bnd_n", "$gpred_nzr.$t $x $1i $" },
  { "nzr_of_nzr_rel", "$gpred_nzr.$t $x $1x $2i $" },
  { "nzr_of_nzr_rel_rev", "$gpred_nzr.$t $1x $x $2i $" },

  { "rel_refl", "$gpred_rel.$t $x $i $" },
  { "bnd_of_nzr_rel", "$gpred_rel.$t $2x $1x $i $1p $2p" },
  { "rel_of_nzr_bnd", "$gpred_rel.$t $x $1x $2i $1p $2p" },
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
  { "float_of_fix_flt", "$gfloat.$t _ $1x $1c _ $2c _ $" },
  { "fix_float_of_fix", "$gfloat.$t _ _ _ $1c $c $1x $" },
  { "flt_float_of_flt", "$gfloat.$t _ _ _ $1c $c $1x $" },

  { "float_round_dn", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_round_up", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_round_zr", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_round_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_round_na", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_enforce", "$gfloat.$t _ _ _ _ $1i $i $" },
  { "float_absolute_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_absolute_na", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_absolute_wide_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_absolute_inv_ne", "$gfloat.$t _ _ _ $1i $i $" },
  { "float_absolute_inv_na", "$gfloat.$t _ _ _ $1i $i $" },
  { "float_relative_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_relative_na", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_relative_inv_ne", "$gfloat.$t _ _ $y $1i $i $" },
  { "float_relative_inv_na", "$gfloat.$t _ _ $y $1i $i $" },
  { "rel_of_fix_float_ne", "$gfloat.$t _ _ $1c $1x $i $" },
  { "rel_of_fix_float_na", "$gfloat.$t _ _ $1c $1x $i $" },

  { "fix_of_fixed", "$gfixed.$t _ _ _ $c $" },
  { "fixed_of_fix", "$gfixed.$t _ $1x $1c _ $" },
  { "fix_fixed_of_fix", "$gfixed.$t _ _ $1c $c $1x $" },
  { "flt_fixed_of_flt", "$gfixed.$t _ _ $1c $c $1x $" },
  { "bnd_of_bnd_fix", "$gfixed.$t $1x $2c $1i $i $" },

  { "fixed_round_dn", "$gfixed.$t _ $1x $1i $i $" },
  { "fixed_round_up", "$gfixed.$t _ $1x $1i $i $" },
  { "fixed_round_zr", "$gfixed.$t _ $1x $1i $i $" },
  { "fixed_round_ne", "$gfixed.$t _ $1x $1i $i $" },
  { "fixed_error_dn", "$gfixed.$t _ _ $i $" },
  { "fixed_error_ne", "$gfixed.$t _ _ $i $" },

  { "bnd_rewrite", "$grewriting.$t $1x $1y $i $1p $2p" },
  { "abs_rewrite", "$grewriting.$t $1x $1y $i $1p $2p" },
  { "fix_rewrite", "$grewriting.$t $1x $1y $c $1p $2p" },
  { "flt_rewrite", "$grewriting.$t $1x $1y $c $1p $2p" },
  { "nzr_rewrite", "$grewriting.$t $1x $1y $1p $2p" },
  { "rel_rewrite_1", "$grewriting.$t $1x $1y $y $i $1p $2p" },
  { "rel_rewrite_2", "$grewriting.$t $1x $1y $x $i $1p $2p" },
  { "eql_trans", "$grewriting.$t $x $1y $y $1p $2p" },

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
  { "div_fil", "$grewriting.$t $1x $2x $i $1p $2p" },
  { "div_fir", "$grewriting.$t $2x $1x $i $1p $2p" },
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

  { "opp_fibe", "$grewriting.$t $1x $1y $1p" },
  { "add_file", "$grewriting.$t _ $1x $1y $1p" },
  { "add_fire", "$grewriting.$t $1x _ $1y $1p" },
  { "sub_file", "$grewriting.$t _ $1x $1y $1p" },
  { "sub_fire", "$grewriting.$t $1x _ $1y $1p" },
  { "mul_file", "$grewriting.$t _ $1x $1y $1p" },
  { "mul_fire", "$grewriting.$t $1x _ $1y $1p" },
  { "div_file", "$grewriting.$t _ $1x $1y $1p" },
  { "div_fire", "$grewriting.$t $1x _ $1y $1p" },

  { NULL, NULL }
};

theorem_map theorems;

RUN_ONCE(fill_theorem_map)
{
  for (char const *(*p)[2] = theorem_defs; (*p)[0]; ++p) {
    theorems.insert(std::pair<std::string, char const *>((*p)[0], (*p)[1]));
  }
};

bool fqn = false;
bool vernac = true;

static std::string qualify(std::string const &path)
{
  if (fqn) return path;
  else return std::string();
}

std::string convert_name(std::string const &name)
{
  if (!fqn && name == "sqrt") return "sqrtG";
  std::string::size_type p0 = name.find(',');
  if (p0 == std::string::npos) return name;
  std::string prefix = name.substr(0, p0);
  std::string::size_type p1 = name.find(',', p0 + 1);
  std::ostringstream res;
  if (prefix == "rounding_fixed")
  {
    assert(p1 != std::string::npos);
    res << '(' << qualify(FLOCQDEF "generic_fmt.") << "round "
        << qualify(GAPPADEF) << "radix2 ("
        << qualify(FLOCQDEF "FIX.") << "FIX_exp ("
        << name.substr(p1 + 1) << ")) ";
    round_mode:
    assert(p1 == p0 + 3);
    std::string mode = name.substr(p0 + 1, 2);
    if (mode == "ne") res << qualify(FLOCQDEF "rnd_ne.") << "rndNE";
    else res << qualify(FLOCQDEF "generic_fmt.") << "rnd"
             << (char)std::toupper(mode[0]) << (char)std::toupper(mode[1]);
    res << ") ";
    return res.str();
  }
  if (prefix == "rounding_float")
  {
    std::string::size_type p2 = name.find(',', p1 + 1);
    assert(p2 != std::string::npos);
    res << '(' << qualify(FLOCQDEF "generic_fmt.") << "round "
        << qualify(GAPPADEF) << "radix2 ("
        << qualify(FLOCQDEF "FLT.") << "FLT_exp ("
        << name.substr(p2 + 1) << ") (" << name.substr(p1 + 1, p2 - p1 - 1) << ")) ";
    goto round_mode;
  }
  bool fragile = false;
  res << prefix;
  do {
    std::string::size_type p1 = p0 + 1;
    p0 = name.find(',', p1);
    std::string s(name, p1, p0 == std::string::npos ? p0 : p0 - p1);
    if (!std::isalpha(s[0])) {
      res << " (" << s << ')';
      fragile = true;
    } else res << '_' << s;
  } while (p0 != std::string::npos);
  if (!fragile) return res.str();
  return '(' + res.str() + ')';
}

static id_cache< std::string > displayed_floats;

std::string display(number const &f)
{
  std::ostringstream s;
  bool zero;
  int exp;
  s << '(' << get_real_split(f, exp, zero);
  s << ") (" << (zero ? 0 : exp) << ')';
  std::string const &s_ = s.str();
  int f_id = displayed_floats.find(s_);
  std::string name = composite('f', f_id);
  if (f_id < 0) return name;
  *out << (vernac ? "Definition " : "let ") << name << " := "
       << qualify(GAPPADEF) << "Float2 " << s_
       << (vernac ? ".\n" : " in\n");
  return name;
}

static id_cache< std::string > displayed_intervals;

std::string display(interval const &i)
{
  std::ostringstream s;
  s << display(lower(i)) << ' ' << display(upper(i));
  std::string const &s_ = s.str();
  int i_id = displayed_intervals.find(s_);
  std::string name = composite('i', i_id);
  if (i_id < 0) return name;
  *out << (vernac ? "Definition " : "let ") << name << " := "
       << qualify(GAPPADEF) << "makepairF " << s_
       << (vernac ? ".\n" : " in\n");
  return name;
}

static id_cache< ast_real const * > displayed_reals;

std::ostream *out_vars;

std::string display(ast_real const *r)
{
  if (hidden_real const *h = boost::get< hidden_real const >(r))
    r = h->real;
  int r_id = displayed_reals.find(r);
  std::string name = r->name ? '_' + r->name->name : composite('r', r_id);
  if (r_id < 0)
    return name;
  if (boost::get< undefined_real const >(r)) {
    *out_vars << (vernac ? "Variable " : " (") << name << " : "
              << qualify(COQRDEF) << 'R' << (vernac ? ".\n" : ")");
    return name;
  }
  auto_flush plouf;
  plouf << (vernac ? "Notation " : "let ") << name << " := ";
  if (vernac) plouf << '(';
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r))
  {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0)
      plouf << qualify("Gappa.Gappa_pred_bnd.") << "Float1 0";
    else if (n.exponent == 0)
      plouf << qualify("Gappa.Gappa_pred_bnd.") << "Float1 (" << m << ')';
    else
      plouf << qualify(GAPPADEF) << "float" << n.base << "R ("
            << qualify(GAPPADEF) << "Float" << n.base
            << " (" << m << ") (" << n.exponent << "))";
  }
  else if (real_op const *o = boost::get< real_op const >(r))
  {
    static char const op[] = "X-XX+-*/XX";
    if (o->type == ROP_FUN)
    {
      std::string description = o->fun->description();
      plouf << convert_name(description) << ' ' << display(o->ops[0]);
      for (ast_real_vect::const_iterator i = ++(o->ops.begin()),
           end = o->ops.end(); i != end; ++i)
        plouf << ' ' << display(*i);
    }
    else if (fqn)
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
    else if (o->ops.size() == 1)
    {
      std::string s(1, op[o->type]);
      if (o->type == UOP_ABS) s = "Rabs";
      else if (o->type == UOP_SQRT) s = "sqrt";
      plouf << '(' << s << ' ' << display(o->ops[0]) << ")%R";
    }
    else
    {
      plouf << '(' << display(o->ops[0]) << ' ' << op[o->type] << ' '
            << display(o->ops[1]) << ")%R";
    }
  }
  else
    assert(false);
  plouf << (vernac ? ").\n" : " in\n");
  return name;
}

static id_cache< std::string > displayed_properties;

std::string display(property const &p)
{
  std::ostringstream s;
  predicate_type t = p.real.pred();
  ast_real const *real = p.real.real();
  if (p.null())
  {
    return qualify(GAPPADEF) + "contradiction";
  }
  else if (p.real.pred_bnd())
  {
    interval const &bnd = p.bnd();
    if (lower(bnd) == number::neg_inf) {
      assert(t == PRED_BND);
      if (fqn)
        s << COQRDEF "Rle " << display(real) << ' ' << display(upper(bnd));
      else
        s << '(' << display(real) << " <= " << display(upper(bnd)) << ")%R";
    } else if (upper(bnd) == number::pos_inf) {
      assert(t == PRED_BND);
      if (fqn)
        s << COQRDEF "Rle " << display(lower(bnd)) << ' ' << display(real);
      else
        s << '(' << display(lower(bnd)) << " <= " << display(real) << ")%R";
    }
    else
    {
      switch (t) {
      case PRED_BND:
        s << qualify(GAPPADEF) << "BND " << display(real) << ' ' << display(bnd);
        break;
      case PRED_ABS:
        s << qualify(GAPPADEF) << "ABS " << display(real) << ' ' << display(bnd);
        break;
      case PRED_REL:
        s << qualify(GAPPADEF) << "REL " << display(real) << ' '
          << display(p.real.real2()) << ' ' << display(bnd);
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
      s << qualify(GAPPADEF) << "FIX " << display(real) << " (" << p.cst() << ')';
      break;
    case PRED_FLT:
      s << qualify(GAPPADEF) << "FLT " << display(real) << " (" << p.cst() << ')';
      break;
    case PRED_EQL:
      s << display(real) << " = " << display(p.real.real2());
      break;
    case PRED_NZR:
      s << qualify(GAPPADEF) << "NZR " << display(real);
      break;
    default:
      assert(false);
    }
  }
  std::string s_ = s.str();
  int p_id = displayed_properties.find(s_);
  std::string name = composite('p', p_id);
  if (p_id >= 0)
    *out << (vernac ? "Notation " : "let ") << name << (vernac ? " := (" : " := ")
         << s_ << (vernac ? "). (* " : " in (* ") << dump_property(p) << " *)\n";
  return name;
}

void apply_theorem(auto_flush &plouf, std::string const &th,
  property const &res, property const *hyp, property_map const *pmap, int *num)
{
  theorem_map::const_iterator it = theorems.find(th);
  if (it == theorems.end())
  {
    plouf << "UNKNOWN_" << th;
    return;
  }
  char const *p = it->second.c_str();
  bool has_comp = false;
  int max = 0;
  std::string buf;
  for (; *p; ++p)
  {
    if (*p != '$') { plouf << *p; continue; }
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
      case 'g': {
        char const *q = strchr(p + 1, '.');
        assert(q);
        plouf << qualify("Gappa.Gappa_" + std::string(p + 1, q + 1));
        p = q;
        break; }
      case 't': plouf << th; break;
      case 'i': plouf << display(h->bnd()); break;
      case 'l': plouf << display(lower(h->bnd())); break;
      case 'u': plouf << display(upper(h->bnd())); break;
      case 'c': plouf << '(' << h->cst() << ')'; break;
      case 'x': plouf << display(h->real.real()); break;
      case 'y': plouf << display(h->real.real2()); break;
      case '\0':
        has_comp = true;
        p = buf.c_str();
        break;
      case 'p':
        plouf << 'h';
        if (pmap) {
          property_map::const_iterator pki = pmap->find(h->real);
          assert(pki != pmap->end());
          plouf << pki->second.first;
        } else if (num)
          plouf << num[h - hyp];
        else
          plouf << h - hyp;
        break;
      case 'b':
        has_comp = true;
        break;
      default:
        plouf << '$';
    }
  }
  if (has_comp) plouf << " _";
}

std::string display(theorem_node *t)
{
  static int t_id = 0;
  std::string name = composite('t', ++t_id);
  auto_flush plouf;
  if (vernac)
  {
    plouf << "Lemma " << name << " : ";
    for (property_vect::const_iterator i = t->hyp.begin(),
         end = t->hyp.end(); i != end; ++i)
      plouf << display(*i) << " -> ";
    plouf << display(t->res) << ".\n";
    int nb_hyps = t->hyp.size();
    if (nb_hyps)
    {
      plouf << " intros";
      for (int i = 0; i < nb_hyps; ++i) plouf << " h" << i;
      plouf << ".\n";
    }
    plouf << " refine (";
  }
  else
  {
    plouf << "let " << name;
    int num_hyp = 0;
    for (property_vect::const_iterator i = t->hyp.begin(),
         i_end = t->hyp.end(); i != i_end; ++i)
      plouf << " (h" << num_hyp++ << " : " << display(*i) << ')';
    plouf << " : " <<  display(t->res) << " := ";
  }

  apply_theorem(plouf, convert_name(t->name), t->res, &*t->hyp.begin());
  plouf << (vernac ? ") ; finalize.\nQed.\n" : " in\n");
  return name;
}

std::string subset_name(property const &p1, property const &p2)
{
  assert(p1.implies(p2));
  if (p2.implies(p1)) return std::string();
  char const *prefix = "", *suffix = "";
  switch (p1.real.pred()) {
  case PRED_BND:
    if (lower(p2.bnd()) == number::neg_inf)
      suffix = "_r";
    else if (upper(p2.bnd()) == number::pos_inf)
      suffix = "_l";
    break;
  case PRED_ABS: prefix = "abs_"; break;
  case PRED_REL: prefix = "rel_"; break;
  case PRED_FIX: prefix = "fix_"; break;
  case PRED_FLT: prefix = "flt_"; break;
  case PRED_EQL:
  case PRED_NZR: assert(false);
  }
  return std::string(prefix) + "subset" + suffix;
}

void invoke_lemma(auto_flush &plouf, property_vect const &hyp, property_map const &pmap)
{
  for (property_vect::const_iterator j = hyp.begin(),
       j_end = hyp.end(); j != j_end; ++j)
  {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    std::string sn = subset_name(*pki->second.second, *j);
    if (sn.empty()) {
      if (vernac) plouf << " exact h" << h << '.';
      else plouf << " h" << h;
    } else {
      plouf << (vernac ? " refine (" : " (");
      apply_theorem(plouf, sn, *j, pki->second.second, &pmap);
      plouf << (vernac ? ") ; finalize." : ")");
    }
  }
  if (vernac) plouf << '\n';
}

void invoke_lemma(auto_flush &plouf, node *n, property_map const &pmap)
{
  if (n->type != HYPOTHESIS) {
    if (vernac) plouf << " apply " << display(n) << '.';
    else plouf << display(n);
    invoke_lemma(plouf, n->graph->get_hypotheses(), pmap);
  } else {
    property_vect hyp;
    hyp.push_back(n->get_result());
    invoke_lemma(plouf, hyp, pmap);
  }
}

static void invoke_subset(auto_flush &plouf, property const p1, property const &p2)
{
  std::string sn = subset_name(p1, p2);
  if (sn.empty()) return;
  plouf << " apply " << sn << " with ";
  switch (p1.real.pred()) {
  case PRED_FIX: plouf << p1.cst() << "%Z"; break;
  case PRED_FLT: plouf << p1.cst() << "%positive"; break;
  default: plouf << display(p1.bnd());
  }
  plouf << ". 2: finalize.\n";
}

static id_cache< node * > displayed_nodes;

std::string display(node *n)
{
  assert(n);
  int n_id = displayed_nodes.find(n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  if (vernac) plouf << "Lemma " << name << " : ";
  else plouf << "let "<< name;
  property_vect const &n_hyp = n->graph->get_hypotheses();
  property_map pmap;
  int num_hyp = 0;
  for (property_vect::const_iterator i = n_hyp.begin(),
       i_end = n_hyp.end(); i != i_end; ++i)
  {
    property const &p = *i;
    if (vernac) plouf << display(p) << " -> ";
    pmap[p.real] = std::make_pair(num_hyp++, &p);
  }
  node_vect const &pred = n->get_subproofs();
  property const &n_res = n->get_result();
  std::string p_res, prefix;
  if (n_res.null()) {
    p_res = qualify(GAPPADEF) + "contradiction";
    prefix = "absurd_";
  } else
    p_res = display(n_res);
  plouf << (vernac ? "" : " : ") << p_res << (vernac ? ". (* " : " := (* ")
        << (!n_res.null() ? dump_property(n_res) : "contradiction") << " *)\n";
  if (vernac && num_hyp) {
    plouf << " intros";
    for(int i = 0; i < num_hyp; ++i) plouf << " h" << i;
    plouf << ".\n";
  }
  switch (n->type) {
  case MODUS: {
    for (node_vect::const_iterator i = pred.begin(),
         i_end = pred.end(); i != i_end; ++i)
    {
      node *m = *i;
      property const &res = m->get_result();
      plouf << (vernac ? " assert (h" : "  let h") << num_hyp << " : "
            << display(res) << (vernac ? ")." : " := ");
      if (vernac) invoke_lemma(plouf, m, pmap);
      else plouf << display(m) << " in\n";
      pmap[res.real] = std::make_pair(num_hyp++, &res);
    }
    modus_node *mn = dynamic_cast< modus_node * >(n);
    assert(mn && mn->target);
    plouf << (vernac ? " apply " : "  ") << display(mn->target);
    if (vernac) plouf << '.';
    invoke_lemma(plouf, mn->target->hyp, pmap);
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
      plouf << (vernac ? " assert (h" : "  let h") << num_hyp << " : "
            << display(res) << (vernac ? ")." : " := ");
      invoke_lemma(plouf, m, pmap);
      if (!vernac) plouf << " in\n";
      num[i] = num_hyp++;
    }
    if (vernac) {
      plouf << " apply " << prefix << "intersect" << suffix << " with"
               " (1 := h" << num[0] << ") (2 := h" << num[1] << ")."
               " finalize.\n";
    } else {
      plouf << "  ";
      apply_theorem(plouf, std::string(prefix) + "intersect" + suffix,
                    n_res, hyps, NULL, num);
    }
    break; }
  case UNION: {
    assert(vernac);
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
      if (!res.null()) // not a contradictory result
        invoke_subset(plouf, res, n_res);
      invoke_lemma(plouf, m, pmap);
      if (i + 1 != i_end)
        plouf << " next_interval (union) u.\n";
      else
        plouf << " exact u.\n";
    }
    break; }
  case GOAL: {
    node *m = pred[0];
    if (vernac) {
      invoke_subset(plouf, m->get_result(), n_res);
      invoke_lemma(plouf, m, pmap);
    } else {
      property const &res = m->get_result();
      std::string sn = subset_name(res, n_res);
      if (!sn.empty()) {
        plouf << "  let h" << num_hyp << " : " << display(res) << " := "
              << display(m) << " in ";
        pmap[res.real] = std::make_pair(num_hyp++, &res);
        apply_theorem(plouf, sn, n_res, &res, &pmap);
      } else
        plouf << "  " << display(m);
    }
    break; }
  default:
    assert(false);
  }
  plouf << (vernac ? "Qed.\n" : " in\n");
  return name;
}

void reset()
{
  displayed_nodes.clear();
}

}
