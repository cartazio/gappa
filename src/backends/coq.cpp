#include <cctype>
#include <iostream>
#include <ostream>
#include <sstream>
#include "utils.hpp"
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"

extern std::string get_real_split(number const &f, int &exp, bool &zero);

template< class T >
int map_finder(std::map< T, int > &m, T const &k) {
  typename std::map< T, int >::const_iterator it = m.find(k);
  if (it != m.end()) return -it->second;
  int id = m.size() + 1;
  m.insert(std::make_pair(k, id));
  return id;
}

static std::string composite(char prefix, int num) {
  std::ostringstream s;
  s << prefix << (num < 0 ? -num : num);
  return s.str();
}

static std::string convert_name(std::string const &name) {
  if (name == "sqrt") return "sqrtG";
  std::string::size_type p2 = name.find(',');
  if (p2 == std::string::npos) return name;
  std::string prefix = name.substr(0, p2);
  bool rounding = prefix == "rounding_fixed" || prefix == "rounding_float";
  bool fragile = false;
  std::ostringstream res;
  res << prefix;
  do {
    std::string::size_type p1 = p2 + 1;
    p2 = name.find(',', p1);
    std::string s(name, p1, p2 == std::string::npos ? p2 : p2 - p1);
    if (!std::isalpha(s[0])) {
      res << " (" << s << ')';
      fragile = true;
    } else if (rounding && s.length() == 2) {
      res << " round" << (char)std::toupper(s[0]) << (char)std::toupper(s[1]);
      fragile = true;
    } else res << '_' << s;
  } while (p2 != std::string::npos);
  if (!fragile) return res.str();
  return '(' + res.str() + ')';
}

static std::map< std::string, int > displayed_floats;

static std::string display(number const &f) {
  std::ostringstream s;
  bool zero;
  int exp;
  s << '(' << get_real_split(f, exp, zero);
  s << ") (" << (zero ? 0 : exp) << ')';
  std::string const &s_ = s.str();
  int f_id = map_finder(displayed_floats, s_);
  std::string name = composite('f', f_id);
  if (f_id >= 0)
    *out << "Definition " << name << " := Float2 " << s_ << ".\n";
  return name;
}

static std::map< std::string, int > displayed_intervals;

static std::string display(interval const &i) {
  std::ostringstream s;
  s << display(lower(i)) << ' ' << display(upper(i));
  std::string const &s_ = s.str();
  int i_id = map_finder(displayed_intervals, s_);
  std::string name = composite('i', i_id);
  if (i_id >= 0)
    *out << "Definition " << name << " := makepairF " << s_ << ".\n";
  return name;
}

static std::map< ast_real const *, int > displayed_reals;

static std::string display(ast_real const *r) {
  int r_id = map_finder(displayed_reals, r);
  std::string name = r->name ? '_' + r->name->name : composite('r', r_id);
  if (r_id < 0)
    return name;
  if (boost::get< undefined_real const >(r)) {
    *out << "Variable " << name << " : R.\n";
    return name;
  }
  auto_flush plouf;
  plouf << "Notation " << name << " := (";
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r)) {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0) plouf << "Float1 0";
    else if (n.exponent == 0) plouf << "Float1 (" << m << ')';
    else plouf << "Float" << n.base << " (" << m << ") (" << n.exponent << ')';
  } else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "X-XX+-*/XX";
    if (o->type == ROP_FUN) {
      plouf << convert_name(o->fun->name()) << " (" << display(o->ops[0]) << ')';
      for(ast_real_vect::const_iterator i = ++(o->ops.begin()), end = o->ops.end(); i != end; ++i)
        plouf << " (" << display(*i) << ')';
    } else if (o->ops.size() == 1) {
      std::string s(1, op[o->type]);
      if (o->type == UOP_ABS) s = "Rabs";
      else if (o->type == UOP_SQRT) s = "sqrt";
      plouf << '(' << s << ' ' << display(o->ops[0]) << ")%R";
    } else
      plouf << '(' << display(o->ops[0]) << ' ' << op[o->type] << ' ' << display(o->ops[1]) << ")%R";
  } else assert(false);
  plouf << ").\n";
  return name;
}

static std::map< std::string, int > displayed_properties;

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
    default: assert(false);
    }
  }
  std::string s_ = s.str();
  int p_id = map_finder(displayed_properties, s_);
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

static void invoke_lemma(auto_flush &plouf, property_vect const &hyp, property_map const &pmap) {
  for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j) {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    predicate_type t = j->real.pred();
    if (j->real.pred_bnd()) {
      interval const &i = pki->second.second->bnd(), &ii = j->bnd();
      assert(i <= ii);
      if (ii <= i)
        plouf << " exact h" << h << '.';
      else
        plouf << " apply " << (t == PRED_ABS ? "abs_" : "") << "subset with (1 := h" << h << "). finalize.";
    } else {
      long c = pki->second.second->cst(), cc = j->cst();
      assert(t == PRED_FIX && c >= cc || t == PRED_FLT && c <= cc);
      if (c == c)
        plouf << " exact h" << h << '.';
      else
        plouf << " apply " << (t == PRED_FIX ? "fix" : "flt") << "_subset with (1 := h" << h << "). finalize.";
    }
  }
  plouf << '\n';
}

static void invoke_lemma(auto_flush &plouf, node *n, property_map const &pmap) {
  if (n->type != HYPOTHESIS) {
    plouf << " apply " << display(n) << '.';
    invoke_lemma(plouf, n->get_hypotheses(), pmap);
  } else {
    property_vect hyp;
    hyp.push_back(n->get_result());
    invoke_lemma(plouf, hyp, pmap);
  }
}

static std::map< node *, int > displayed_nodes;

static std::string display(node *n) {
  assert(n);
  int n_id = map_finder(displayed_nodes, n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  plouf << "Lemma " << name << " : ";
  property_vect const &n_hyp = n->get_hypotheses();
  property_map pmap;
  int num_hyp = 0;
  for(property_vect::const_iterator i = n_hyp.begin(), end = n_hyp.end();
      i != end; ++i) {
    property const &p = *i;
    plouf << display(p) << " -> ";
    pmap.insert(std::make_pair(p.real, std::make_pair(num_hyp++, &p)));
  }
  node_vect const &pred = n->get_subproofs();
  if (n->type == GOAL && pred[0]->type == HYPOTHESIS) {
    property const &p = pred[0]->get_result();
    plouf << display(p) << " -> ";
    assert(num_hyp == 0);
    pmap.insert(std::make_pair(p.real, std::make_pair(num_hyp++, &p)));
  }
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
    std::string suffix;
    for(int i = 0; i < 2; ++i) {
      node *m = pred[i];
      property const &res = m->get_result();
      if (!is_bounded(res.bnd())) suffix = (i == 0) ? "_hb" : "_bh";
      else if (res.real.pred() != PRED_BND) suffix = "_aa";
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
        plouf << " next_interval (" << prefix << "union) u.\n";
      else
        plouf << " exact u.\n";
    }
    plouf << "Qed.\n";
    break; }
  case GOAL: {
    node *m = pred[0];
    interval const &mb = m->get_result().bnd(), &nb = n_res.bnd();
    if (!(nb <= mb))
      plouf << " apply subset with " << display(mb) << ". 2: finalize.\n";
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
    o << "Require Import Gappa_library.\n"
         "Section Generated_by_Gappa.\n";
  }
  void finalize() { *out << "End Generated_by_Gappa.\n"; }
  virtual std::string rewrite(ast_real const *, ast_real const *);
  virtual std::string theorem(node *n) { return display(n); }
};

std::string coq_backend::rewrite(ast_real const *src, ast_real const *dst) {
  static int a_id = 0;
  std::string name = composite('a', ++a_id);
  auto_flush plouf;
  plouf << "Hypothesis " << name << " : forall zi : FF, BND "
        << display(dst) << " zi -> true = true -> BND " << display(src) << " zi.\n";
  return name;
}

static struct coq_backend dummy;
