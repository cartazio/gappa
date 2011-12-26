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
#include "backends/coq_common.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"

#define GAPPADEF "Gappa.Gappa_definitions."
#define COQRDEF "Reals.Rdefinitions."
#define FLOCQDEF "Flocq.Core.Fcore_"

std::ostream *out_vars;

extern std::string get_real_split(number const &f, int &exp, bool &zero);

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
    *out_vars << " (" << name << " : " COQRDEF "R)";
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
    else
      plouf << GAPPADEF "float" << n.base << "R (" GAPPADEF "Float" << n.base
            << " (" << m << ") (" << n.exponent << "))";
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
    case PRED_EQL:
      s << display(real) << " = " << display(p.real.real2());
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
  for (property_vect::const_iterator j = hyp.begin(),
       j_end = hyp.end(); j != j_end; ++j)
  {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    std::string sn = subset_name(*pki->second.second, *j);
    if (sn.empty())
      plouf << " h" << h;
    else
      apply_theorem(plouf, sn, *j, pki->second.second, &pmap);
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
    property const &res = m->get_result();
    std::string sn = subset_name(res, n_res);
    if (!sn.empty()) {
      plouf << "  let h" << num_hyp << " : " << display(res) << " := "
        << display(m) << " in ";
      pmap[res.real] = std::make_pair(num_hyp++, &res);
      apply_theorem(plouf, sn, n_res, &res, &pmap);
    } else
      plouf << "  " << display(m);
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
  void initialize(std::ostream &o) { out = &o; fqn = true; }
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
  *out << " *)\n(";
  std::ostringstream buf_var, buf_lem, buf_hyp, buf_prf;
  std::ostream *old_out;
  old_out = out;
  out_vars = &buf_var;
  out = &buf_lem;
  property_vect const &n_hyp = n->graph->get_hypotheses();
  int num_hyp = 0;
  for (property_vect::const_iterator i = n_hyp.begin(),
       i_end = n_hyp.end(); i != i_end; ++i)
  {
    buf_hyp << " (h" << num_hyp << " : " << display(*i) << ')';
    ++num_hyp;
  }
  out = &buf_prf;
  std::string s = display(n);
  out = old_out;
  if (!buf_var.str().empty()) *out << "fun" << buf_var.str() << " =>\n";
  *out << buf_lem.str();
  if (num_hyp) *out << "fun" << buf_hyp.str() << " =>\n";
  *out << buf_prf.str() << s << ")\n";
  return s;
}

static struct coq_lambda_backend dummy;
