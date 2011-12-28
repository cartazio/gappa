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

struct coq_lambda_backend: backend
{
  coq_lambda_backend(): backend("coq-lambda") {}
  void initialize(std::ostream &o) { out = &o; fqn = true; vernac = false; }
  void finalize() {}
  void reset() { coq::reset(); }
  std::string rewrite(ast_real const *, ast_real const *, pattern_cond_vect const &);
  std::string theorem(node *n);
  bool is_known(std::string const &s) { return theorems.count(s); }
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
