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

typedef std::map< std::string, int > float_map; // (not so) bastard way of doing it
static float_map displayed_floats;

int display(number const &f) {
  std::stringstream s;
  bool zero;
  int exp;
  s << '(' << get_real_split(f, exp, zero);
  s << ") (" << (zero ? 0 : exp) << ')';
  std::string const &s_ = s.str();
  int f_id = map_finder(displayed_floats, s_);
  if (f_id < 0) return -f_id;
  std::cout << "Definition f" << f_id << " := Float " << s_ << ".\n";
  return f_id;
}

typedef std::map< std::string, int > interval_map; // (not so) bastard way of doing it
static interval_map displayed_intervals;

int display(interval const &i) {
  std::stringstream s;
  s << 'f' << display(lower(i)) << " f" << display(upper(i));
  std::string const &s_ = s.str();
  int i_id = map_finder(displayed_intervals, s_);
  if (i_id < 0) return -i_id;
  std::cout << "Definition i" << i_id << " := makepairF " << s_ << ".\n";
  return i_id;
}

typedef std::map< ast_real const *, int > real_map;
static real_map displayed_reals;

int display(ast_real const *r) {
  int r_id = map_finder(displayed_reals, r);
  if (r_id < 0) return -r_id;
  auto_flush plouf;
  plouf << "Definition r" << r_id << " := ";
  if (ast_ident const *v = r->get_variable()) {
    std::cout << "Variable _" << v->name << " : R.\n";
    plouf << '_' << v->name;
  } else if (ast_number const *const *nn = boost::get< ast_number const *const >(r)) {
    ast_number const &n = **nn;
    std::string m = (n.mantissa.size() > 0 && n.mantissa[0] == '+') ? n.mantissa.substr(1) : n.mantissa;
    if (n.base == 0) plouf << "Float1 0";
    else if (n.exponent == 0) plouf << "Float1 (" << m << ')';
    else plouf << "Float" << n.base << " (" << m << ") (" << n.exponent << ')';
  } else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "-+-*/";
    if (o->ops.size() == 1)
      plouf << '(' << op[o->type] << " r" << display(o->ops[0]) << ")%R";
    else
      plouf << "(r" << display(o->ops[0]) << ' ' << op[o->type] << " r" << display(o->ops[1]) << ")%R";
  } else if (rounded_real const *rr = boost::get< rounded_real const >(r))
    plouf << "rounding_" << rr->rounding->name() << " r" << display(rr->rounded);
  else assert(false);
  plouf << ".\n";
  return r_id;
}

typedef std::map< std::string, int > property_map; // (not so) bastard way of doing it
static property_map displayed_properties;

int display(property const &p) {
  std::stringstream s;
  s << display(p.bnd) << " r" << display(p.real);
  std::string s_ = s.str();
  int p_id = map_finder(displayed_properties, s_);
  if (p_id < 0) return -p_id;
  std::cout << "Definition p" << p_id << " := IintF i" << s_ << ".\n";
  return p_id;
}

typedef std::map< node *, int > disp_node_map;
static disp_node_map displayed_nodes;

int display(node *n) {
  int n_id = map_finder(displayed_nodes, n);
  if (n_id < 0) return -n_id;
  auto_flush plouf;
  plouf << (n->type == AXIOM ? "Hypothesis l" : "Lemma l") << n_id << " : ";
  property_vect const &n_hyp = n->get_hypotheses();
  for(property_vect::const_iterator i = n_hyp.begin(), end = n_hyp.end(); i != end; ++i)
    plouf << 'p' << display(*i) << " -> ";
  int p_res = display(n->get_result());
  plouf << 'p' << p_res << '.';
  if (n->type == AXIOM) {
    plouf << '\n';
    return n_id;
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
    plouf << " unfold p" << p_res << ".\n apply " << t->name;
    if (nb_hyps) {
      plouf << " with";
      for(int i = 0; i < nb_hyps; ++i) plouf << " (" << i + 1 << " := h" << i << ')';
    }
    plouf << ".\n reflexivity.\nQed.\n";
    break; }
  case MODUS: {
    plouf << '\n';
    typedef std::map< ast_real const *, int > property_map;
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end(); j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, num_hyp));
    node_vect const &pred = n->get_subproofs();
    for(node_vect::const_iterator i = ++pred.begin(), i_end = pred.end(); i != i_end; ++i, ++num_hyp) {
      node *m = *i;
      property const &res = m->get_result();
      plouf << " assert (h" << num_hyp << " : p" << display(res) << "). apply l" << display(m) << '.';
      property_vect const &m_hyp = m->get_hypotheses();
      for(property_vect::const_iterator j = m_hyp.begin(), j_end = m_hyp.end(); j != j_end; ++j) {
        property_map::iterator pki = pmap.find(j->real);
        assert(pki != pmap.end());
        plouf << " exact h" << pki->second << '.';
      }
      pmap.insert(std::make_pair(res.real, num_hyp));
      plouf << '\n';
    }
    node *m = pred[0];
    plouf << " apply l" << display(m) << '.';
    property_vect const &m_hyp = m->get_hypotheses();
    for(property_vect::const_iterator j = m_hyp.begin(), j_end = m_hyp.end(); j != j_end; ++j) {
      property_map::iterator pki = pmap.find(j->real);
      assert(pki != pmap.end());
      plouf << " exact h" << pki->second << '.';
    }
    plouf << "\nQed.\n";
    break; }
  case INTERSECTION: {
    plouf << '\n';
    typedef std::map< ast_real const *, int > property_map;
    property_map pmap;
    int num_hyp = 0;
    for(property_vect::const_iterator j = n_hyp.begin(), j_end = n_hyp.end(); j != j_end; ++j, ++num_hyp)
      pmap.insert(std::make_pair(j->real, num_hyp));
    node_vect const &pred = n->get_subproofs();
    int num[2];
    for(int i = 0; i < 2; ++i) {
      node *m = pred[i];
      property const &res = m->get_result();
      if (m->type == HYPOTHESIS) {
        property_map::iterator pki = pmap.find(res.real);
        assert(pki != pmap.end());
        num[i] = pki->second;
        continue;
      }
      plouf << " assert (h" << num_hyp << " : p" << display(res) << "). apply l" << display(m) << '.';
      property_vect const &m_hyp = m->get_hypotheses();
      for(property_vect::const_iterator j = m_hyp.begin(), j_end = m_hyp.end(); j != j_end; ++j) {
        property_map::iterator pki = pmap.find(j->real);
        assert(pki != pmap.end());
        plouf << " exact h" << pki->second << '.';
      }
      plouf << '\n';
      num[i] = num_hyp++;
    }
    plouf << " apply intersect with (1 := h" << num[0] << ") (2 := h" << num[1] << ").\n"
             " reflexivity.\nQed.\n";
    break; }
  case UNION: {
    plouf << "\n union";
    node_vect const &pred = n->get_subproofs();
    for(node_vect::const_iterator i = pred.begin(), end = pred.end(); i != end; ++i)
      plouf << " l" << display(*i);
    plouf << ".\nQed.\n";
    break; }
  default:
    assert(false);
  }
  return n_id;
}

extern std::vector< graph_t * > graphs;

int main() {
  yyparse();
  for(std::vector< graph_t * >::const_iterator i = graphs.begin(), i_end = graphs.end(); i != i_end; ++i) {
    graph_t *g = *i;
    graph_loader loader(g);
    property_vect const &goals = g->prover.goals;
    int nb = goals.size();
    g->prover.ordered_reals = new ast_real_vect;
    ast_real_vect &all_reals = *g->prover.ordered_reals;
    std::vector< bool > scheme_results(nb);
    {
      ast_real_vect dummy;
      for(int j = 0; j < nb; ++j) 
        scheme_results[j] = generate_scheme_tree(goals[j].real, all_reals, dummy);
    }
    g->prover();
    delete g->prover.ordered_reals;
    clear_schemes();
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
      if (ast_ident const *v = p.real->get_variable())
        std::cerr << v->name;
      else
        std::cerr << "...";
      std::cerr << " in " << p.bnd << '\n';
    }
    for(int j = 0; j < nb; ++j)
      if (results[j]) {
        std::cout << "\n\nRequire Import IA_comput.\nRequire Import IA_manip.\n";
        break;
      }
    for(int j = 0; j < nb; ++j)
      if (results[j]) display(results[j]);
    delete g;
  }
  return 0;
}
