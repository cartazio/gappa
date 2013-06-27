/*
   Copyright (C) 2013 - 2013 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <cassert>
#include <iostream>
#include <sstream>
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast_real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"

extern std::string get_real_split(number const &f, int &exp, bool &zero);

static std::string convert_name(std::string const &name)
{
  size_t p = name.find_first_of("_<>");
  if (p == std::string::npos) return name;
  std::string buf;
  size_t o = 0;
  do {
    buf += name.substr(o, p - o);
    switch (name[p]) {
    case '_': buf += "\\_"; break;
    case '<': buf += "\\langle "; break;
    case '>': buf += "\\rangle "; break;
    default: assert(false);
    }
    o = p + 1;
    p = name.find_first_of("_<>", o);
  } while (p != std::string::npos);
  buf += name.substr(o);
  return buf;
}

static std::string display(number const &f)
{
  bool zero;
  int exp;
  std::string t = get_real_split(f, exp, zero);
  if (zero) return "0";
  if (!exp) return t;
  std::ostringstream s;
  s << t << " \\cdot 2^{" << exp << '}';
  return s.str();
}

static std::string display(interval const &i)
{
  std::ostringstream s;
  s << '[' << display(lower(i)) << ',' << display(upper(i)) << ']';
  return s.str();
}

static std::string display(ast_real const *r, unsigned prio = 0)
{
  if (hidden_real const *h = boost::get< hidden_real const >(r))
    r = h->real;
  if (r->name)
    return "\\mathit{" + convert_name(r->name->name) + "}";
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r)) {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0) return "0";
    if (n.exponent == 0) return m;
    std::ostringstream s;
    s << m << " \\cdot " << n.base << "^{" << n.exponent << "}";
    return s.str();
  }
  if (real_op const *o = boost::get< real_op const >(r))
  {
    if (o->type == ROP_FUN)
    {
      std::ostringstream s;
      s << "\\mathrm{" << convert_name(o->fun->pretty_name()) << "}(";
      bool first = true;
      for (ast_real_vect::const_iterator i = o->ops.begin(),
           i_end = o->ops.end(); i != i_end; ++i)
      {
        if (first) first = false;
        else s << ", ";
        s << display(*i, 0);
      }
      s << ')';
      return s.str();
    }
    static unsigned const pr[] = { 0, 2, 0, 0, 0, 0, 1, 0, 0, 0 };
    std::string t = display(o->ops[0], pr[o->type]);
    std::ostringstream s;
    if (o->ops.size() == 1) {
      switch (o->type) {
      case UOP_ABS:
        s << "\\left| " << t << " \\right|";
        prio = 0;
        break;
      case UOP_SQRT:
        s << "\\sqrt{" << t << '}';
        prio = 0;
        break;
      case UOP_NEG:
        s << '-' << t;
        break;
      default:
        assert(false);
      }
    } else {
      std::string u = display(o->ops[1], o->type == BOP_DIV ? 0 : pr[o->type] + 1);
      switch (o->type) {
      case BOP_ADD:
        s << t << " + " << u;
        break;
      case BOP_SUB:
        s << t << " - " << u;
        break;
      case BOP_MUL:
        s << t << " \\times " << u;
        break;
      case BOP_DIV:
        s << "\\frac{" << t << "}{" << u << '}';
        prio = 0;
        break;
      default:
        assert(false);
      }
    }
    if (prio <= pr[o->type]) return s.str();
    return "\\left( " + s.str() + " \\right)";
  }
  assert(false);
  return "...";
}

static std::string display(property const &p)
{
  if (p.real.null()) return "\\bot";
  std::ostringstream s;
  std::string r = display(p.real.real());
  switch (p.real.pred()) {
  case PRED_BND: s << r; break;
  case PRED_ABS: s << "\\left| " << r << " \\right|"; break;
  case PRED_REL: s << r << " \\diamond " << display(p.real.real2()); break;
  case PRED_FIX: s << "\\mathrm{FIX}\\left( " << r << " \\right) = " << p.cst(); break;
  case PRED_FLT: s << "\\mathrm{FLT}\\left(" << r << " \\right) = " << p.cst(); break;
  case PRED_EQL: s << r << " = " << display(p.real.real2()); break;
  case PRED_NZR: s << r << " \\neq 0"; break;
  }
  if (!p.real.pred_bnd()) return s.str();
  interval const &bnd = p.bnd();
  if (p.real.pred() == PRED_ABS && lower(bnd) == 0) {
    s << " \\le " << display(upper(bnd));
  } else if (p.real.pred() != PRED_ABS && upper(bnd) == -lower(bnd) && upper(bnd) != 0) {
    r = s.str();
    s.str(std::string());
    s << "\\left| " << r << " \\right| \\le" << display(upper(bnd));
  } else if (lower(bnd) == number::neg_inf) {
    s << " \\le " << display(upper(bnd));
  } else if (upper(bnd) == number::pos_inf) {
    s << " \\ge " << display(lower(bnd));
  } else {
    s << " \\in " << display(bnd);
  }
  return s.str();
}

static id_cache<node *> displayed_nodes;

static graph_t *last_graph;

static std::string display(node *n)
{
  assert(n);
  int n_id = displayed_nodes.find(n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  node_vect const &pred = n->get_subproofs();
  std::vector<std::string> hyps;
  for (node_vect::const_iterator i = pred.begin(),
       i_end = pred.end(); i != i_end; ++i)
  {
    node *n = *i;
    if (n->type == HYPOTHESIS) continue;
    hyps.push_back(display(*i));
  }
  if (n->graph != last_graph) {
    last_graph = n->graph;
    property_vect const &g_hyp = n->graph->get_hypotheses();
    if (g_hyp.empty()) {
      std::cout << "\n\\bigskip\\noindent\nOne can deduce the following properties:\n";
    } else {
      std::cout << "\n\\bigskip\\noindent\nUnder the following hypotheses\n";
      for (property_vect::const_iterator i = g_hyp.begin(),
           i_end = g_hyp.end(); i != i_end; ++i)
      {
        std::cout << "\\[" << display(*i) << ",\\]\n";
      }
      std::cout << "one can deduce the following properties:\n";
    }
  }
  std::cout << "\\begin{equation}\\label{" << name << "}\n"
    << display(n->get_result()) << "\n\\end{equation}\nby using";
  bool first = true;
  for (std::vector<std::string>::const_iterator i = hyps.begin(),
       i_end = hyps.end(); i != i_end; ++i)
  {
    if (first) first = false;
    else std::cout << ',';
    std::cout << " (\\ref{" << *i << "})";
  }
  if (!first) std::cout << ", and";
  switch (n->type) {
  case MODUS:
    std::cout << " theorem \\texttt{"
      << convert_name(dynamic_cast<modus_node *>(n)->target->name) << '}';
    break;
  case INTERSECTION:
    std::cout << " performing an intersection";
    break;
  case UNION:
    std::cout << " performing an union";
    break;
  case GOAL:
    std::cout << " concluding";
    break;
  default:
    assert(false);
  }
  std::cout << ".\n";
  return name;
}

struct latex_backend: backend
{
  latex_backend(): backend("latex") {}
  void initialize(std::ostream &o) { out = &o;
    std::cout << "\\documentclass{article}\n\\begin{document}\n"; }
  void finalize() { std::cout << "\\end{document}\n"; }
  void reset() { displayed_nodes.clear(); }
  virtual std::string rewrite(ast_real const *, ast_real const *, pattern_cond_vect const &);
  virtual std::string theorem(node *n) { return display(n); }
};

std::string latex_backend::rewrite(ast_real const *src, ast_real const *dst, pattern_cond_vect const &)
{
  static int a_id = 0;
  std::ostringstream name;
  name << "rewriting " << ++a_id;
  std::cout << "\\noindent\nLet us assume that the following equality holds.\n"
    "\\begin{equation}\n" << display(src)
    << " = " << display(dst) << ".\n\\end{equation}\n";
  return name.str();
}

static struct latex_backend dummy;
