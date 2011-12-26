/*
   Copyright (C) 2004 - 2012 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cassert>
#include <sstream>
#include "backends/backend.hpp"
#include "backends/coq_common.hpp"
#include "numbers/interval_utility.hpp"
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

  { "mul_rr", "$gpred_rel.$t $1x $1y $2x $2y $1i $2i $i $" },
  { "div_rr", "$gpred_rel.$t $1x $1y $2x $3x $1i $2i $i $" },
  { "compose", "$gpred_rel.$t $1x $1y $2y $1i $2i $i $" },
  { "compose_swap", "$gpred_rel.$t $1x $y $2x $3x $1i $2i $i $" },

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

  { "rel_refl", "$gpred_rel.$t $1x $i $" },
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
  { "float_relative_ne", "$gfloat.$t _ _ $1x $1i $i $" },
  { "float_relative_na", "$gfloat.$t _ _ $1x $1i $i $" },
  { "rel_of_fix_float_ne", "$gfloat.$t _ _ $1c $1x $i $" },
  { "rel_of_fix_float_na", "$gfloat.$t _ _ $1c $1x $i $" },

  { "fix_of_fixed", "$gfixed.$t _ _ _ $c $" },
  { "fixed_of_fix", "$gfixed.$t _ $1x $1c _ $i $" },
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

static std::string qualify(std::string const &path, std::string const &name)
{
  if (!fqn) return name;
  return path + name;
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
    res << '(' << qualify(FLOCQDEF "generic_fmt.", "round") << ' '
        << qualify(GAPPADEF, "radix2") << " ("
        << qualify(FLOCQDEF "FIX.", "FIX_exp") << " ("
        << name.substr(p1 + 1) << ")) ";
    round_mode:
    assert(p1 == p0 + 3);
    std::string mode = name.substr(p0 + 1, 2);
    if (mode == "ne") res << qualify(FLOCQDEF "rnd_ne.", "rndNE");
    else res << qualify(FLOCQDEF "generic_fmt.", "rnd")
             << (char)std::toupper(mode[0]) << (char)std::toupper(mode[1]);
    res << ") ";
    return res.str();
  }
  if (prefix == "rounding_float")
  {
    std::string::size_type p2 = name.find(',', p1 + 1);
    assert(p2 != std::string::npos);
    res << '(' << qualify(FLOCQDEF "generic_fmt.", "round") << ' '
        << qualify(GAPPADEF, "radix2") << " ("
        << qualify(FLOCQDEF "FLT.", "FLT_exp") << " ("
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
       << qualify(GAPPADEF, "Float2") << ' ' << s_
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
       << qualify(GAPPADEF, "makepairF") << ' ' << s_
       << (vernac ? ".\n" : " in\n");
  return name;
}

}
