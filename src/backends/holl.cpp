/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <map>
#include <iostream>
#include <sstream>
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"

extern std::string get_real_split(number const &f, int &exp, bool &zero, bool);

static std::string convert_name(std::string const &name)
{
  if (name == "sqrt") return "sqrtG";
  std::string::size_type p0 = name.find(',');
  if (p0 == std::string::npos) return name;
  std::string prefix = name.substr(0, p0);
  std::string::size_type p1 = name.find(',', p0 + 1);
  std::ostringstream res;
  if (prefix == "rounding_float")
  {
    std::string::size_type p2 = name.find(',', p1 + 1);
    assert(p2 != std::string::npos);
    assert(p1 == p0 + 3);
    std::string dir = name.substr(p0 + 1, 2);
    if (dir == "ne") dir = "Nearest";
    else if (dir == "zr") dir = "Zero";
    else if (dir == "up") dir = "Up";
    else if (dir == "dn") dir = "Down";
    int prec = std::atoi(name.substr(p1 + 1, p2 - p1 - 1).c_str());
    int exp = std::atoi(name.substr(p2 + 1).c_str());
    res << "round (" << (exp - prec) * 2 + 4 << ',' << prec << ',' << exp << ") " << dir;
    return res.str();
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

static std::string display(number const &f)
{
  std::ostringstream s;
  bool zero;
  int exp;
  std::string t = get_real_split(f, exp, zero, false);
  if (zero)
    s << "&0";
  else if (t[0] == '-') {
    t[0] = '&';
    s << "--(" << t << ')';
  } else s << '&' << t;
  if (!zero && exp != 0)
    s << (exp < 0 ? " / &2 pow " : " * &2 pow ") << std::abs(exp);
  std::string const &s_ = s.str();
  int f_id = displayed_floats.find(s_);
  std::string name = composite('f', f_id);
  if (f_id < 0) return name;
  *out << "NOTATION `(" << name << ":real) = " << s_ << "`;;\n";
  return name;
}

static id_cache< std::string > displayed_intervals;

static std::string display(interval const &i)
{
  std::ostringstream s;
  s << display(lower(i)) << ":real),(" << display(upper(i));
  std::string const &s_ = s.str();
  int i_id = displayed_intervals.find(s_);
  std::string name = composite('i', i_id);
  if (i_id < 0) return name;
  *out << "NOTATION `(" << name << ":real#real) = ((" << s_ << ":real))`;;\n";
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
    *out << "VARIABLE `" << name << ": real`;;\n";
    return name;
  }
  auto_flush plouf;
  plouf << "NOTATION `(" << name << ":real) = ";
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r))
  {
    ast_number const &n = **nn;
    if (n.base == 0) plouf << "&0";
    else {
      std::string t = n.mantissa;
      assert(t.size() > 0 && (t[0] == '+' || t[0] == '-'));
      bool neg = t[0] == '-';
      t[0] = '&';
      if (neg) plouf << "--(" << t << ')';
      else plouf << t;
      if (n.exponent != 0)
        plouf << ' ' << (n.exponent < 0 ? '/' : '*') << " &" << n.base << " pow " << std::abs(n.exponent);
    }
  }
  else if (real_op const *o = boost::get< real_op const >(r))
  {
    static char const op[] = "X-XX+-*/XX";
    if (o->type == ROP_FUN) {
      plouf << convert_name(o->fun->description());
      for(ast_real_vect::const_iterator i = o->ops.begin(), end = o->ops.end(); i != end; ++i)
        plouf << " (" << display(*i) << ":real)";
    } else if (o->ops.size() == 1) {
      std::string s(1, op[o->type]);
      switch (o->type) {
      case UOP_NEG: s = "--"; break;
      case UOP_ABS: s = "abs"; break;
      case UOP_SQRT: s = "sqrt"; break;
      default: assert(false);
      }
      plouf << '(' << s << " (" << display(o->ops[0]) << ":real))";
    } else
      plouf << '(' << display(o->ops[0]) << ":real) " << op[o->type] << " (" << display(o->ops[1]) << ":real)";
  }
  else
    assert(false);
  plouf << "`;;\n";
  return name;
}

static id_cache<property> displayed_properties;

static std::string display(property const &p)
{
  if (p.null()) return "F";
  int p_id = displayed_properties.find(p);
  std::string name = composite('p', p_id);
  if (p_id < 0) return name;
  std::ostringstream s;
  predicate_type t = p.real.pred();
  ast_real const *real = p.real.real();
  if (p.real.pred_bnd())
  {
    interval const &bnd = p.bnd();
    if (lower(bnd) == number::neg_inf) {
      assert(t == PRED_BND);
      s << "((" << display(real) << ":real) <= (" << display(upper(bnd)) << ":real))";
    } else if (upper(bnd) == number::pos_inf) {
      assert(t == PRED_BND);
      s << "((" << display(lower(bnd)) << ":real) <= (" << display(real) << ":real))";
    } else {
      switch (t) {
      case PRED_BND:
        s << "BND (" << display(real) << ":real) (" << display(bnd) << ":real#real)";
        break;
      case PRED_ABS:
        s << "ABS (" << display(real) << ":real) (" << display(bnd) << ":real#real)";
        break;
      case PRED_REL:
        s << "REL (" << display(real) << ":real) (" << display(p.real.real2())
          << ":real) (" << display(bnd) << ":real#real)";
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
      s << "FIX (" << display(real) << ":real) (" << p.cst() << ')';
      break;
    case PRED_FLT:
      s << "FLT (" << display(real) << ":real) (" << p.cst() << ')';
      break;
    case PRED_EQL:
      s << "EQL (" << display(real) << ":real) (" << display(p.real.real2()) << ":real)";
      break;
    case PRED_NZR:
      s << "NZR (" << display(real) << ":real)";
      break;
    default:
      assert(false);
    }
  }
  *out << "NOTATION `(" << name << ":bool) = " << s.str() << "`;; (* "
       << dump_property(p) << " *)\n";
  return name;
}

static property const &fetch(property const &p)
{
  if (p.real.pred_bnd() && !is_defined(p.bnd())) {
    undefined_map::const_iterator i = instances->find(p.real);
    assert(i != instances->end());
    return i->second;
  }
  return p;
}

static id_cache<property_tree> displayed_trees;

static std::string display(property_tree const &t)
{
  if (t.empty()) return "F";
  if (t.atom && t.conjunction) return display(fetch(*t.atom));
  int t_id = displayed_trees.find(t);
  std::string name = composite('s', t_id);
  if (t_id < 0) return name;
  auto_flush plouf;
  plouf << "NOTATION `(" << name << ":bool) = ";
  if (!t.left) {
    assert(!t.conjunction);
    plouf << "~ " << display(fetch(*t.atom));
  } else {
    plouf << display(*t.left) << (t.conjunction ? " /\\ " : " \\/ ")
      << display(*t.right);
  }
  plouf << "`;;\n";
  return name;
}

static std::string display(theorem_node *t)
{
  static int t_id = 0;
  std::string name = composite('t', ++t_id);
  auto_flush plouf;
  plouf << "LEMMA \"" << name << "\" `(";
  for (property_vect::const_iterator i = t->hyp.begin(),
       end = t->hyp.end(); i != end; ++i)
    plouf << display(*i) << ":bool) ==> (";
  plouf << display(t->res) << ":bool)`;;\n";
  int nb_hyps = t->hyp.size();
  if (nb_hyps)
  {
    plouf << " INTROS [\"h0\"";
    for(int i = 1; i < nb_hyps; ++i) plouf << "; \"h" << i << '"';
    plouf << "];;\n";
  }
  plouf << " APPLY " << convert_name(t->name) << " [";
  if (nb_hyps)
  {
    plouf << "\"h0\"";
    for (int i = 1; i < nb_hyps; ++i)
      plouf << "; \"h" << i << '"';
  }
  plouf << "] THEN FINALIZE ();;\nQED ();;\n";
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
  for (property_vect::const_iterator j = hyp.begin(),
       j_end = hyp.end(); j != j_end; ++j)
  {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    std::string sn = subset_name(*pki->second.second, *j);
    if (sn.empty())
      plouf << " EXACT \"h" << h << "\";;";
    else
      plouf << " APPLY \"" << sn << "\" [\"h" << h << "\"] THEN FINALIZE ();;";
  }
  plouf << '\n';
}

static std::string display(node *n);

/**
 * Instantiate node @a m as "h @a num_hyp" with the hypotheses of node @a n.
 */
static void pose_hypothesis(auto_flush &plouf, int num_hyp, node *m, node *n)
{
  plouf << " ASSERT \"h" << num_hyp << "\" `(";
  int i = 0;
  graph_t *g = n->graph;
  for (; g != m->graph; g = g->get_father()) ++i;
  if (m->type == LOGIC && !static_cast<logic_node *>(m)->before) {
    plouf << 'h' << i;
  } else {
    plouf << display(m);
    for (; g; g = g->get_father()) plouf << " h" << (i++);
  }
  plouf << ":bool)`;;\n";
}

typedef std::map<ast_real const *, int> real_map;

static int find_real(real_map &rm, ast_real const *r)
{
  real_map::const_iterator i = rm.find(r);
  if (i == rm.end()) {
    int j = rm.size();
    rm[r] = j;
    return j;
  }
  return i->second;
}

static void invoke_subset(auto_flush &plouf, property const p1, property const &p2)
{
  std::string sn = subset_name(p1, p2);
  if (sn.empty()) return;
  plouf << " APPLY \"" << sn << "\" [";
  switch (p1.real.pred()) {
  case PRED_FIX:
  case PRED_FLT: plouf << p1.cst(); break;
  default: plouf << "\"" << display(p1.bnd()) << "\"";
  }
  plouf << "] THEN FINALIZE ();;\n";
}

static void simplification(auto_flush &plouf, property_tree const &before, property_tree const &after, property const &mod, int num_hyp)
{
  plouf << " SIMPLIFY ();;\n";
}

static void select(auto_flush &plouf, int idx, int num_hyp)
{
  plouf << " EXACT `(";
  if (idx) plouf << "proj" << idx << ' ';
  plouf << 'h' << num_hyp << ")`;;\n";
}

static id_cache< node * > displayed_nodes;

static std::string display(node *n)
{
  assert(n);
  int n_id = displayed_nodes.find(n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  plouf << "LEMMA \"" << name << "\" `(";
  int num_hyp = 0;
  for (graph_t *g = n->graph; g; g = g->get_father())
  {
    plouf << display(g->get_hypotheses()) << ":bool) ==> (";
    ++num_hyp;
  }
  logic_node *ln = NULL;
  if (n->type == LOGIC) {
    ln = static_cast<logic_node *>(n);
    assert(ln->before);
    plouf << display(ln->tree) << ":bool)`;;\n";
  } else {
    property const &n_res = n->get_result();
    if (n_res.null())
      plouf << "F:bool)`;;\n";
    else
      plouf << display(n_res) << ":bool)`;; (* " << dump_property(n_res) << " *)\n";
  }
  if (num_hyp) {
    plouf << " INTROS [\"h0\"";
    for (int i = 1; i < num_hyp; ++i) plouf << "; \"h" << i << '"';
    plouf << "];;\n";
  }
  switch (n->type) {
  case LOGIC: {
    pose_hypothesis(plouf, num_hyp, ln->before, n);
    if (ln->modifier) {
      pose_hypothesis(plouf, ++num_hyp, ln->modifier, n);
      simplification(plouf, ln->before->tree, ln->tree, ln->modifier->get_result(), num_hyp);
    } else {
      assert(ln->before->tree.conjunction);
      select(plouf, ln->index, num_hyp);
    }
    break; }
  case LOGICP: {
    logicp_node *ln = static_cast<logicp_node *>(n);
    assert(ln->before && ln->before->tree.conjunction);
    pose_hypothesis(plouf, num_hyp, ln->before, n);
    select(plouf, ln->index, num_hyp);
    break; }
  case MODUS: {
    property_map pmap;
    node_vect const &pred = n->get_subproofs();
    for (node_vect::const_iterator i = pred.begin(),
         i_end = pred.end(); i != i_end; ++i)
    {
      node *m = *i;
      pose_hypothesis(plouf, num_hyp, m, n);
      property const &res = m->get_result();
      pmap[res.real] = std::make_pair(num_hyp++, &res);
    }
    modus_node *mn = static_cast<modus_node *>(n);
    assert(mn->target);
    plouf << " PARTIAL_APPLY \"" << display(mn->target) << "\";;";
    invoke_lemma(plouf, mn->target->hyp, pmap);
    break; }
  case INTERSECTION: {
    node_vect const &pred = n->get_subproofs();
    int num[2];
    char const *suffix ="", *prefix = "";
    property const &n_res = n->get_result();
    if (n_res.null()) prefix = "absurd_";
    for (int i = 0; i < 2; ++i)
    {
      node *m = pred[i];
      property const &res = m->get_result();
      switch (res.real.pred()) {
        case PRED_BND:
          if (is_bounded(res.bnd())) break;
	  if (!i) suffix = "_hb";
	  else if (suffix[0]) suffix = "_hh";
	  else suffix = "_bh";
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
      pose_hypothesis(plouf, num_hyp, m, n);
      num[i] = num_hyp++;
    }
    plouf << " APPLY " << prefix << "intersect" << suffix <<
             " [\"h" << num[0] << "\"; \"h" << num[1] << "\"] THEN"
             " FINALIZE ();;\n";
    break; }
  case UNION: {
    plouf << " UNION ();;\n";
    break; }
  }
  plouf << "QED ();;\n";
  return name;
}

struct holl_backend: backend {
  holl_backend(): backend("holl") {}
  void initialize(std::ostream &o) {
    out = &o;
  }
  void finalize() {}
  virtual std::string rewrite(ast_real const *, ast_real const *, pattern_cond_vect const &);
  virtual std::string theorem(node *n) { return display(n); }
};

std::string holl_backend::rewrite(ast_real const *src, ast_real const *dst,
                                  pattern_cond_vect const &)
{
  static int a_id = 0;
  std::ostringstream name;
  name << ++a_id;
  auto_flush plouf;
  plouf << "HYPOTHESIS \"a" << name.str() << "\" `!(zi:real#real). BND ("
        << display(dst) << ":real) zi ==> BND (" << display(src) << ":real) zi`;;\n";
  return name.str();
}

static struct holl_backend dummy;
