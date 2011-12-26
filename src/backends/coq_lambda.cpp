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

using namespace coq;

static std::string display(node *n);

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
  void initialize(std::ostream &o) { out = &o; fqn = true; vernac = false; }
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
