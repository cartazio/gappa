/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cctype>
#include <iostream>
#include <ostream>
#include <sstream>
#include "utils.hpp"
#include "backends/backend.hpp"
#include "backends/coq_common.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/proof_graph.hpp"

using namespace coq;

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
    *out << "Variable " << name << " : R.\n";
    return name;
  }
  auto_flush plouf;
  plouf << "Notation " << name << " := (";
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r))
  {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0) plouf << "Float1 0";
    else if (n.exponent == 0) plouf << "Float1 (" << m << ')';
    else plouf << "float" << n.base << "R (Float" << n.base
               << " (" << m << ") (" << n.exponent << "))";
  } else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "X-XX+-*/XX";
    if (o->type == ROP_FUN)
    {
      std::string description = o->fun->description();
      plouf << convert_name(description) << " (" << display(o->ops[0]) << ')';
      for (ast_real_vect::const_iterator i = ++(o->ops.begin()),
           end = o->ops.end(); i != end; ++i)
        plouf << " (" << display(*i) << ')';
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
  else assert(false);
  plouf << ").\n";
  return name;
}

static id_cache< std::string > displayed_properties;

static std::string display(property const &p) {
  std::ostringstream s;
  predicate_type t = p.real.pred();
  ast_real const *real = p.real.real();
  if (p.real.pred_bnd()) {
    interval const &bnd = p.bnd();
    if (lower(bnd) == number::neg_inf) {
      assert(t == PRED_BND);
      s << '(' << display(real) << " <= " << display(upper(bnd)) << ")%R";
    } else if (upper(bnd) == number::pos_inf) {
      assert(t == PRED_BND);
      s << '(' << display(lower(bnd)) << " <= " << display(real) << ")%R";
    } else {
      switch (t) {
      case PRED_BND: s << "BND " << display(real) << ' ' << display(bnd); break;
      case PRED_ABS: s << "ABS " << display(real) << ' ' << display(bnd); break;
      case PRED_REL: s << "REL " << display(real) << ' ' << display(p.real.real2()) << ' ' << display(bnd); break;
      default: assert(false);
      }
    }
  } else {
    switch (t) {
    case PRED_FIX: s << "FIX " << display(real) << " (" << p.cst() << ')'; break;
    case PRED_FLT: s << "FLT " << display(real) << " (" << p.cst() << ')'; break;
    case PRED_EQL: s << display(real) << " = " << display(p.real.real2()); break;
    case PRED_NZR: s << "NZR " << display(real); break;
    default: assert(false);
    }
  }
  std::string s_ = s.str();
  int p_id = displayed_properties.find(s_);
  std::string name = composite('p', p_id);
  if (p_id >= 0)
    *out << "Notation " << name << " := (" << s_ << "). (* " << dump_property(p) << " *)\n";
  return name;
}

static std::string display(node *n);

static std::string display(theorem_node *t) {
  static int t_id = 0;
  std::string name = composite('t', ++t_id);
  auto_flush plouf;
  plouf << "Lemma " << name << " : ";
  for(property_vect::const_iterator i = t->hyp.begin(), end = t->hyp.end(); i != end; ++i)
    plouf << display(*i) << " -> ";
  plouf << display(t->res) << ".\n";
  int nb_hyps = t->hyp.size();
  if (nb_hyps) {
    plouf << " intros";
    for(int i = 0; i < nb_hyps; ++i) plouf << " h" << i;
    plouf << ".\n";
  }
  plouf << " apply " << convert_name(t->name);
  if (nb_hyps) {
    plouf << " with";
    for(int i = 0; i < nb_hyps; ++i) plouf << " (" << i + 1 << " := h" << i << ')';
  }
  plouf << " ; finalize.\nQed.\n";
  return name;
}

typedef std::map< predicated_real, std::pair< int, property const * > > property_map;

static std::string subset_name(property const &p1, property const &p2)
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

static void invoke_lemma(auto_flush &plouf, property_vect const &hyp, property_map const &pmap)
{
  for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j)
  {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    std::string sn = subset_name(*pki->second.second, *j);
    if (sn.empty())
      plouf << " exact h" << h << '.';
    else
      plouf << " apply " << sn << " with (1 := h" << h << "). finalize.";
  }
  plouf << '\n';
}

static void invoke_lemma(auto_flush &plouf, node *n, property_map const &pmap) {
  if (n->type != HYPOTHESIS) {
    plouf << " apply " << display(n) << '.';
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

static std::string display(node *n) {
  assert(n);
  int n_id = displayed_nodes.find(n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  plouf << "Lemma " << name << " : ";
  property_vect const &n_hyp = n->graph->get_hypotheses();
  property_map pmap;
  int num_hyp = 0;
  for(property_vect::const_iterator i = n_hyp.begin(), end = n_hyp.end();
      i != end; ++i) {
    property const &p = *i;
    plouf << display(p) << " -> ";
    pmap.insert(std::make_pair(p.real, std::make_pair(num_hyp++, &p)));
  }
  node_vect const &pred = n->get_subproofs();
  property const &n_res = n->get_result();
  std::string p_res, prefix;
  if (n_res.null()) {
    p_res = "contradiction";
    prefix = "absurd_";
  } else
    p_res = display(n_res);
  plouf << p_res << ". (* " << (!n_res.null() ? dump_property(n_res) : "contradiction") << " *)\n";
  if (num_hyp) {
    plouf << " intros";
    for(int i = 0; i < num_hyp; ++i) plouf << " h" << i;
    plouf << ".\n";
  }
  switch (n->type) {
  case MODUS: {
    for(node_vect::const_iterator i = pred.begin(), i_end = pred.end(); i != i_end; ++i) {
      node *m = *i;
      property const &res = m->get_result();
      plouf << " assert (h" << num_hyp << " : " << display(res) << ").";
      invoke_lemma(plouf, m, pmap);
      pmap[res.real] = std::make_pair(num_hyp++, &res);
    }
    modus_node *mn = dynamic_cast< modus_node * >(n);
    assert(mn && mn->target);
    plouf << " apply " << display(mn->target) << '.';
    invoke_lemma(plouf, mn->target->hyp, pmap);
    plouf << "Qed.\n";
    break; }
  case INTERSECTION: {
    int num[2];
    char const *suffix = "";
    for(int i = 0; i < 2; ++i) {
      node *m = pred[i];
      property const &res = m->get_result();
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
      plouf << " assert (h" << num_hyp << " : " << display(res) << ").";
      invoke_lemma(plouf, m, pmap);
      num[i] = num_hyp++;
    }
    plouf << " apply " << prefix << "intersect" << suffix << " with"
                 " (1 := h" << num[0] << ") (2 := h" << num[1] << ")."
             " finalize.\nQed.\n";
    break; }
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
      if (!res.null()) // not a contradictory result
        invoke_subset(plouf, res, n_res);
      invoke_lemma(plouf, m, pmap);
      if (i + 1 != i_end)
        plouf << " next_interval (union) u.\n";
      else
        plouf << " exact u.\n";
    }
    plouf << "Qed.\n";
    break; }
  case GOAL: {
    node *m = pred[0];
    invoke_subset(plouf, m->get_result(), n_res);
    invoke_lemma(plouf, m, pmap);
    plouf << "Qed.\n";
    break; }
  default:
    assert(false);
  }
  return name;
}

struct coq_backend: backend {
  coq_backend(): backend("coq") {}
  void initialize(std::ostream &o) {
    out = &o;
    o << "Require Import Fcore.\n"
         "Require Import Gappa_library.\n"
         "Section Generated_by_Gappa.\n";
  }
  void finalize() { *out << "End Generated_by_Gappa.\n"; }
  void reset() { displayed_nodes.clear(); }
  virtual std::string rewrite(ast_real const *, ast_real const *, pattern_cond_vect const &);
  virtual std::string theorem(node *n) { return display(n); }
};

std::string coq_backend::rewrite(ast_real const *src, ast_real const *dst,
                                 pattern_cond_vect const &pc)
{
  static int a_id = 0;
  ++a_id;
  int nb_hyps = 0;
  std::ostringstream s_hyps, s_intros, s_bool, s_proof, s_dec;
  bool first_bool = true;
  auto_flush plouf;
  plouf << "Hypothesis a" << a_id << " : ";
  for (pattern_cond_vect::const_iterator i = pc.begin(),
       i_end = pc.end(); i != i_end; ++i)
  {
    std::string var = display(i->real);
    std::string val;
    if (i->type == COND_NZ || i->value == 0) val = "0";
    else
    {
      std::ostringstream val_;
      val_ << "Float1 (" << i->value << ')';
      val = val_.str();
    }
    plouf << '(' << var;
    switch (i->type)
    {
      case COND_NZ:
      case COND_NE: plouf << " <> " << val << ")%R -> "; break;
      case COND_LT: plouf << " < "  << val << ")%R -> "; break;
      case COND_GT: plouf << " > "  << val << ")%R -> "; break;
      case COND_LE: plouf << " <= " << val << ")%R -> "; break;
      case COND_GE: plouf << " >= " << val << ")%R -> "; break;
    }
    if (i->type == COND_NZ)
    {
      s_hyps << "NZR " << var << " -> ";
      s_intros << " h" << nb_hyps;
      s_proof << " exact h" << nb_hyps << ".\n";
    }
    else
    {
      s_hyps << "forall i" << nb_hyps << " : FF, BND " << var << " i" << nb_hyps << " -> ";
      s_intros << " i" << nb_hyps << " h" << nb_hyps;
      std::string s_dec_ = s_dec.str();
      s_dec.str(std::string());
      if (first_bool)
      {
        first_bool = false;
        s_dec << " rename hb into j" << nb_hyps << ".\n";
      }
      else
      {
        s_bool << " && ";
        s_dec << " generalize (andb_prop _ _ hb). clear hb. intros (hb, j" << nb_hyps << ").\n";
      }
      if (i->value == 0)
      {
        char const *s = NULL;
        switch (i->type)
        {
          case COND_LT: s = "lt0"; break;
          case COND_GT: s = "gt0"; break;
          case COND_LE: s = "le0"; break;
          case COND_GE: s = "ge0"; break;
          default: assert(false);
        }
        s_bool << "rewrite_" << s << "_helper i" << nb_hyps;
        s_proof << " apply rewrite_" << s << " with (1 := h" << nb_hyps
                << ") (2 := j" << nb_hyps << ").\n";
      }
      else
      {
        char const *s = NULL;
        switch (i->type)
        {
          case COND_NE: s = "ne"; break;
          case COND_LT: s = "lt"; break;
          case COND_GT: s = "gt"; break;
          case COND_LE: s = "le"; break;
          case COND_GE: s = "ge"; break;
          default: assert(false);
        }
        s_bool << "rewrite_" << s << "_helper i" << nb_hyps << " (" << i->value << ')';
        s_proof << " apply rewrite_" << s << " with (1 := h" << nb_hyps
                << ") (2 := j" << nb_hyps << ").\n";
      }
      s_dec << s_dec_;
    }
    ++nb_hyps;
  }
  plouf << display(src) << " = " << display(dst) << ".\n";
  if (first_bool) s_bool << "true";
  std::string name = composite('b', a_id);
  plouf << "Lemma " << name << " : " << s_hyps.str() << s_bool.str()
        << " = true -> " << display(src) << " = " << display(dst)
        << ".\n intros" << s_intros.str() << " hb.\n" << s_dec.str()
        << " apply a" << a_id << ".\n" << s_proof.str() << "Qed.\n";
  return name;
}

static struct coq_backend dummy;
