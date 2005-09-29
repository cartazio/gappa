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
      plouf << o->fun->name() << " (" << display(o->ops[0]) << ')';
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
  s << display(p.bnd) << ' ' << display(p.real);
  std::string s_ = s.str();
  int p_id = map_finder(displayed_properties, s_);
  std::string name = composite('p', p_id);
  if (p_id >= 0)
    *out << "Notation " << name << " := (IintF " << s_ << ").\n";
  return name;
}

static std::string display(node *n);

typedef std::map< ast_real const *, std::pair< int, interval const * > > property_map;

static void invoke_lemma(auto_flush &plouf, node *m, property_map const &pmap) {
  plouf << " apply " << display(m) << '.';
  property_vect const &m_hyp = m->get_hypotheses();
  for(property_vect::const_iterator j = m_hyp.begin(), j_end = m_hyp.end(); j != j_end; ++j) {
    property_map::const_iterator pki = pmap.find(j->real);
    assert(pki != pmap.end());
    int h = pki->second.first;
    interval const &i = *pki->second.second;
    assert(i <= j->bnd);
    if (j->bnd <= i)
      plouf << " exact h" << h << '.';
    else
      plouf << " apply subset with (1 := h" << h << "). reflexivity.";
  }
  plouf << '\n';
}

static std::map< node *, int > displayed_nodes;

static std::string display(node *n) {
  assert(n);
  int n_id = map_finder(displayed_nodes, n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  plouf << (n->type == AXIOM ? "Hypothesis " : "Lemma ") << name << " : ";
  property_vect const &n_hyp = n->get_hypotheses();
  for(property_vect::const_iterator i = n_hyp.begin(), end = n_hyp.end(); i != end; ++i)
    plouf << display(*i) << " -> ";
  property const &n_res = n->get_result();
  std::string p_res = is_empty(n_res.bnd) ? "(forall P, P)" : display(n_res);
  plouf << p_res << '.';
  if (n->type == AXIOM) {
    plouf << " trivial. Qed.\n";
    return name;
  }
  int nb_hyps = n_hyp.size();
  if (nb_hyps) {
    plouf << "\n intros";
    for(int i = 0; i < nb_hyps; ++i) plouf << " h" << i;
    plouf << '.';
  }
  switch (n->type) {
  case THEOREM: {
    theorem_node *t = static_cast< theorem_node * >(n);
    if (!nb_hyps) plouf << '\n';
    plouf << " apply " << t->name;
    if (nb_hyps) {
      plouf << " with";
      for(int i = 0; i < nb_hyps; ++i) plouf << " (" << i + 1 << " := h" << i << ')';
    }
    plouf << ".\n reflexivity.\nQed.\n";
    break; }
  case MODUS: {
    plouf << '\n';
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end();
        j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, std::make_pair(num_hyp, &j->bnd)));
    node_vect const &pred = n->get_subproofs();
    for(node_vect::const_iterator i = pred.begin(), i_end = pred.end();
        i != i_end; ++i, ++num_hyp) {
      node *m = *i;
      property const &res = m->get_result();
      plouf << " assert (h" << num_hyp << " : " << display(res) << ").";
      invoke_lemma(plouf, m, pmap);
      pmap[res.real] = std::make_pair(num_hyp, &res.bnd);
    }
    modus_node *mn = dynamic_cast< modus_node * >(n);
    assert(mn);
    invoke_lemma(plouf, mn->target, pmap);
    plouf << "Qed.\n";
    break; }
  case INTERSECTION: {
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end();
        j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, std::make_pair(num_hyp, &j->bnd)));
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
    std::string prefix;
    if (is_empty(n_res.bnd)) prefix = "absurd_";
    plouf << " apply " << prefix << "intersect with"
                 " (1 := h" << num[0] << ") (2 := h" << num[1] << ").\n"
             " reflexivity.\nQed.\n";
    break; }
  case UNION: {
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end();
        j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, std::make_pair(num_hyp, &j->bnd)));
    interval const *&hcase = pmap[n_hyp[0].real].second;
    plouf << " generalize h0. clear h0.\n";
    node_vect const &pred = n->get_subproofs();
    for(node_vect::const_iterator i = pred.begin(), i_end = pred.end();
        i != i_end; ++i) {
      node *m = *i;
      property_vect const &m_hyp = m->get_hypotheses();
      hcase = &m_hyp[0].bnd;
      plouf << " assert (u : " << display(m_hyp[0]) << " -> " << p_res << "). intro h0.\n";
      property const &res = m->get_result();
      if (!is_empty(res.bnd)) { // not a contradictory result
        assert(res.bnd <= n_res.bnd);
        if (!(n_res.bnd <= res.bnd))
          plouf << " apply subset with " << display(res.bnd) << ". 2: reflexivity.\n";
      }
      invoke_lemma(plouf, m, pmap);
      if (i + 1 != i_end)
        plouf << " apply union with (1 := u). reflexivity. clear u.\n";
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
  virtual void axiom() {}
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
