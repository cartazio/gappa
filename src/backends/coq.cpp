#include <cctype>
#include <iostream>
#include <ostream>
#include <sstream>
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"

extern std::string get_real_split(number const &f, int &exp, bool &zero);

static std::ostream *out;

struct auto_flush: std::stringstream {
  ~auto_flush() { *::out << this->str(); }
};

template< class T >
int map_finder(std::map< T, int > &m, T const &k) {
  typename std::map< T, int >::const_iterator it = m.find(k);
  if (it != m.end()) return -it->second;
  int id = m.size() + 1;
  m.insert(std::make_pair(k, id));
  return id;
}

static std::string composite(char prefix, int num) {
  std::stringstream s;
  s << prefix << (num < 0 ? -num : num);
  return s.str();
}

static std::string convert_name(std::string const &name) {
  std::string::size_type p2 = name.find(',');
  if (p2 == std::string::npos) return name;
  std::ostringstream res;
  res << '(' << name.substr(0, p2);
  while (p2 != std::string::npos) {
    std::string::size_type p1 = p2 + 1;
    p2 = name.find(',', p1);
    std::string s(name, p1, p2 == std::string::npos ? p2 : p2 - p1);
    if (std::isalpha(s[0])) res << '_' << s;
    else res << " (" << s << ')';
  }
  res << ')';
  return res.str();
}

static std::map< std::string, int > displayed_floats;

static std::string display(number const &f) {
  std::stringstream s;
  bool zero;
  int exp;
  s << '(' << get_real_split(f, exp, zero);
  s << ") (" << (zero ? 0 : exp) << ')';
  std::string const &s_ = s.str();
  int f_id = map_finder(displayed_floats, s_);
  std::string name = composite('f', f_id);
  if (f_id >= 0)
    *out << "Definition " << name << " := Float " << s_ << ".\n";
  return name;
}

static std::map< std::string, int > displayed_intervals;

static std::string display(interval const &i) {
  std::stringstream s;
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
    static char const op[] = "X-X+-*/XX";
    if (o->type == ROP_FUN) {
      plouf << convert_name(o->fun->name()) << " (" << display(o->ops[0]) << ')';
      for(ast_real_vect::const_iterator i = ++(o->ops.begin()), end = o->ops.end(); i != end; ++i)
        plouf << " (" << display(*i) << ')';
    } else if (o->ops.size() == 1) {
      std::string s(1, op[o->type]);
      if (o->type == UOP_ABS) s = "Rabs";
      plouf << '(' << s << ' ' << display(o->ops[0]) << ")%R";
    } else
      plouf << '(' << display(o->ops[0]) << ' ' << op[o->type] << ' ' << display(o->ops[1]) << ")%R";
  } else assert(false);
  plouf << ").\n";
  return name;
}

static std::map< std::string, int > displayed_properties;

static std::string display(property const &p) {
  std::stringstream s;
  predicate_type t = p.real.pred();
  if (t == PRED_BND) s << "IintF " << display(p.bnd());
  else s << (t == PRED_FIX ? "FixP (" : "FltP (") << p.cst() << ')';
  s << ' ' << display(p.real.real());
  std::string s_ = s.str();
  int p_id = map_finder(displayed_properties, s_);
  std::string name = composite('p', p_id);
  if (p_id >= 0)
    *out << "Notation " << name << " := (" << s_ << ").\n";
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
  plouf << ".\n reflexivity.\nQed.\n";
  return name;  
}

typedef std::map< predicated_real, std::pair< int, property const * > > property_map;

static void invoke_lemma(auto_flush &plouf, property_vect const &hyp, property_map const &pmap) {
  for(property_vect::const_iterator j = hyp.begin(), j_end = hyp.end(); j != j_end; ++j) {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    predicate_type t = j->real.pred();
    if (t == PRED_BND) {
      interval const &i = pki->second.second->bnd(), &ii = j->bnd();
      assert(i <= ii);
      if (ii <= i)
        plouf << " exact h" << h << '.';
      else
        plouf << " apply subset with (1 := h" << h << "). reflexivity.";
    } else {
      long c = pki->second.second->cst(), cc = j->cst();
      assert(t == PRED_FIX && c >= cc || t == PRED_FLT && c <= cc);
      if (c == c)
        plouf << " exact h" << h << '.';
      else
        plouf << " apply " << (t == PRED_FIX ? "fix" : "flt") << "subset with (1 := h" << h << "). reflexivity.";
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
  for(property_vect::const_iterator i = n_hyp.begin(), end = n_hyp.end(); i != end; ++i)
    plouf << display(*i) << " -> ";
  property const &n_res = n->get_result();
  std::string p_res, prefix;
  if (n_res.null()) {
    p_res = "contradiction";
    prefix = "absurd_";
  } else
    p_res = display(n_res);
  plouf << p_res << ".\n";
  int nb_hyps = n_hyp.size();
  if (nb_hyps) {
    plouf << " intros";
    for(int i = 0; i < nb_hyps; ++i) plouf << " h" << i;
    plouf << ".\n";
  }
  switch (n->type) {
  case MODUS: {
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end();
        j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, std::make_pair(num_hyp, &*j)));
    node_vect const &pred = n->get_subproofs();
    for(node_vect::const_iterator i = pred.begin(), i_end = pred.end();
        i != i_end; ++i, ++num_hyp) {
      node *m = *i;
      property const &res = m->get_result();
      plouf << " assert (h" << num_hyp << " : " << display(res) << ").";
      invoke_lemma(plouf, m, pmap);
      pmap[res.real] = std::make_pair(num_hyp, &res);
    }
    modus_node *mn = dynamic_cast< modus_node * >(n);
    assert(mn && mn->target);
    plouf << " apply " << display(mn->target) << '.';
    invoke_lemma(plouf, mn->target->hyp, pmap);
    plouf << "Qed.\n";
    break; }
  case INTERSECTION: {
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end();
        j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, std::make_pair(num_hyp, &*j)));
    node_vect const &pred = n->get_subproofs();
    int num[2];
    for(int i = 0; i < 2; ++i) {
      node *m = pred[i];
      property const &res = m->get_result();
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
    plouf << " apply " << prefix << "intersect with"
                 " (1 := h" << num[0] << ") (2 := h" << num[1] << ").\n"
             " reflexivity.\nQed.\n";
    break; }
  case UNION: {
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end();
        j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, std::make_pair(num_hyp, &*j)));
    node_vect const &pred = n->get_subproofs();
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
               " intro h" << hcase.first << ".\n";
      property const &res = m->get_result();
      interval const &mb = res.bnd(), &nb = n_res.bnd();
      if (!res.null()) { // not a contradictory result
        assert(mb <= nb);
        if (!(nb <= mb))
          plouf << " apply subset with " << display(mb) << ". 2: reflexivity.\n";
      }
      invoke_lemma(plouf, m, pmap);
      if (i + 1 != i_end)
        plouf << " apply " << prefix << "union with (1 := u). reflexivity. clear u.\n";
      else
        plouf << " apply u.\n";
    }
    plouf << "Qed.\n";
    break; }
  default:
    assert(false);
  }
  return name;
}

struct coq_backend: backend {
  coq_backend(std::ostream &o): backend(o) {
    ::out = &o;
    out << "Require Import IA_comput.\n"
           "Require Import IA_manip.\n"
           "Require Import IA_float.\n"
           "Section Gappa_generated.\n";
  }
  virtual ~coq_backend() {
    out << "End Gappa_generated.\n";
  }
  virtual std::string rewrite(ast_real const *, ast_real const *);
  virtual void theorem(node *n) {
    assert(n);
    if (n->type == HYPOTHESIS)
      std::cerr << "Warning: proof of triviality will not be generated.\n";
    else display(n);
  }
};

REGISTER_BACKEND(coq);

std::string coq_backend::rewrite(ast_real const *src, ast_real const *dst) {
  static int a_id = 0;
  std::string name = composite('a', ++a_id);
  auto_flush plouf;
  plouf << "Hypothesis " << name << " : forall zi : FF, IintF zi "
        << display(dst) << " -> true = true -> IintF zi " << display(src) << ".\n";
  return name;
}
