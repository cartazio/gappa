#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

#include <iostream>
#include <map>
#include <sstream>

extern int yyparse(void);
extern node *generate_dichotomy_proof(property_vect const &hyp, property &res);
extern node *triviality;
extern std::string get_real_split(number const &f, int &exp, bool &zero);

struct auto_flush: std::stringstream {
  ~auto_flush() { std::cout << this->str(); }
};

template< class T >
int map_finder(std::map< T, int > &m, T const &k) {
  typename std::map< T, int >::const_iterator it = m.find(k);
  if (it != m.end()) return -it->second;
  int id = m.size() + 1;
  m.insert(std::make_pair(k, id));
  return id;
}

std::string composite(char prefix, int num) {
  std::stringstream s;
  s << prefix << (num < 0 ? -num : num);
  return s.str();
}

static std::map< std::string, int > displayed_floats;

std::string display(number const &f) {
  std::stringstream s;
  bool zero;
  int exp;
  s << '(' << get_real_split(f, exp, zero);
  s << ") (" << (zero ? 0 : exp) << ')';
  std::string const &s_ = s.str();
  int f_id = map_finder(displayed_floats, s_);
  std::string name = composite('f', f_id);
  if (f_id >= 0)
    std::cout << "Definition " << name << " := Float " << s_ << ".\n";
  return name;
}

static std::map< std::string, int > displayed_intervals;

std::string display(interval const &i) {
  std::stringstream s;
  s << display(lower(i)) << ' ' << display(upper(i));
  std::string const &s_ = s.str();
  int i_id = map_finder(displayed_intervals, s_);
  std::string name = composite('i', i_id);
  if (i_id >= 0)
    std::cout << "Definition " << name << " := makepairF " << s_ << ".\n";
  return name;
}

static std::map< ast_real const *, int > displayed_reals;

std::string display(ast_real const *r) {
  int r_id = map_finder(displayed_reals, r);
  std::string name = r->name ? '_' + r->name->name : composite('r', r_id);
  if (r_id < 0)
    return name;
  if (boost::get< undefined_real const >(r)) {
    std::cout << "Variable " << name << " : R.\n";
    return name;
  }
  auto_flush plouf;
  plouf << "Definition " << name << " := ";
  if (ast_number const *const *nn = boost::get< ast_number const *const >(r)) {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0) plouf << "Float1 0";
    else if (n.exponent == 0) plouf << "Float1 (" << m << ')';
    else plouf << "Float" << n.base << " (" << m << ") (" << n.exponent << ')';
  } else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "-+-*/";
    if (o->ops.size() == 1)
      plouf << '(' << op[o->type] << ' ' << display(o->ops[0]) << ")%R";
    else
      plouf << '(' << display(o->ops[0]) << ' ' << op[o->type] << ' ' << display(o->ops[1]) << ")%R";
  } else if (rounded_real const *rr = boost::get< rounded_real const >(r))
    plouf << "rounding_" << rr->rounding->name() << ' ' << display(rr->rounded);
  else assert(false);
  plouf << ".\n";
  return name;
}

static std::map< std::string, int > displayed_properties;

std::string display(property const &p) {
  std::stringstream s;
  s << display(p.bnd) << ' ' << display(p.real);
  std::string s_ = s.str();
  int p_id = map_finder(displayed_properties, s_);
  std::string name = composite('p', p_id);
  if (p_id >= 0)
    std::cout << "Definition " << name << " := IintF " << s_ << ".\n";
  return name;
}

std::string display(node *n);

typedef std::map< ast_real const *, std::pair< int, interval const * > > property_map;

void invoke_lemma(auto_flush &plouf, node *m, property_map const &pmap) {
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
      plouf << " unfold " << display(*j) << ". apply subset with (1 := h" << h << "). reflexivity.";
  }
  plouf << '\n';
}

static std::map< node *, int > displayed_nodes;

std::string display(node *n) {
  int n_id = map_finder(displayed_nodes, n);
  std::string name = composite('l', n_id);
  if (n_id < 0) return name;
  auto_flush plouf;
  plouf << (n->type == AXIOM ? "Hypothesis " : "Lemma ") << name << " : ";
  property_vect const &n_hyp = n->get_hypotheses();
  for(property_vect::const_iterator i = n_hyp.begin(), end = n_hyp.end(); i != end; ++i)
    plouf << display(*i) << " -> ";
  std::string p_res = display(n->get_result());
  plouf << p_res << '.';
  if (n->type == AXIOM) {
    plouf << '\n';
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
    plouf << " unfold " << p_res << ".\n apply ";
    ast_real_vect subs = t->sub_expressions();
    if (subs.empty()) plouf << t->name;
    else {
      plouf << '(' << t->name;
      for(ast_real_vect::const_iterator i = subs.begin(), i_end = subs.end(); i != i_end; ++i)
        plouf << ' ' << display(*i);
      plouf << ')';
    }
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
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end(); j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, std::make_pair(num_hyp, &j->bnd)));
    node_vect const &pred = n->get_subproofs();
    for(node_vect::const_iterator i = ++pred.begin(), i_end = pred.end(); i != i_end; ++i, ++num_hyp) {
      node *m = *i;
      property const &res = m->get_result();
      plouf << " assert (h" << num_hyp << " : " << display(res) << ").";
      invoke_lemma(plouf, m, pmap);
      pmap.insert(std::make_pair(res.real, std::make_pair(num_hyp, &res.bnd)));
    }
    invoke_lemma(plouf, pred[0], pmap);
    plouf << "Qed.\n";
    break; }
  case INTERSECTION: {
    plouf << " unfold " << p_res << ".\n";
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end(); j != j_end; ++j, ++num_hyp)
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
    plouf << " apply intersect with (1 := h" << num[0] << ") (2 := h" << num[1] << ").\n"
             " reflexivity.\nQed.\n";
    break; }
  case UNION: {
    plouf << "\n (*union";
    node_vect const &pred = n->get_subproofs();
    for(node_vect::const_iterator i = pred.begin(), end = pred.end(); i != end; ++i)
      plouf << ' ' << display(*i);
    plouf << ".*)\nAdmitted.\n";
    break; }
  default:
    assert(false);
  }
  return name;
}

extern std::vector< graph_t * > graphs;

int main() {
  yyparse();
  for(std::vector< graph_t * >::const_iterator i = graphs.begin(), i_end = graphs.end(); i != i_end; ++i) {
    graph_t *g = *i;
    graph_loader loader(g);
    property_vect const &goals = g->prover.goals;
    int nb = goals.size();
    std::vector< bool > scheme_results(nb);
    {
      proof_scheme_list *schemes = new proof_scheme_list;
      g->prover.ordered_schemes = schemes;
      ast_real_vect dummy;
      for(int j = 0; j < nb; ++j) 
        scheme_results[j] = generate_scheme_tree(goals[j].real, *schemes, dummy);
      g->prover();
      for(proof_scheme_list::const_iterator j = schemes->begin(), j_end = schemes->end(); j != j_end; ++j)
        delete *j;
      delete schemes;
      g->prover.ordered_schemes = NULL;
      clear_schemes();
    }
    node_vect results(nb);
    std::cerr << "\n\n";
    for(int j = 0; j < nb; ++j) {
      node *n = find_proof(goals[j]);
      results[j] = n;
      if (!n) {
        std::cerr << (scheme_results[j] ? "no proof\n" : "no scheme\n");
        continue;
      }
      property const &p = n->get_result();
      std::cerr << dump_real(p.real) << " in " << p.bnd << '\n';
    }
    for(int j = 0; j < nb; ++j)
      if (results[j]) {
        std::cout << "\n\nRequire Import IA_comput.\nRequire Import IA_manip.\nRequire Import IA_float.\n";
        break;
      }
    for(int j = 0; j < nb; ++j)
      if (results[j]) display(results[j]);
    delete g;
  }
  return 0;
}
