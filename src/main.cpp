#include "ast.hpp"
#include "basic_proof.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"

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
  std::cout << "Definition i" << i_id << " := makepairR " << s_ << ".\n";
  return i_id;
}

typedef std::map< ast_real const *, int > real_map;
static real_map displayed_reals;

int display(ast_real const *r) {
  int r_id = map_finder(displayed_reals, r);
  if (r_id < 0) return -r_id;
  auto_flush plouf;
  plouf << "Definition r" << r_id << " := ";
  if (ast_ident const *v = r->get_variable())
    plouf << '_' << v->name;
  else if (ast_number const *const *n = boost::get< ast_number const *const >(r))
    if ((*n)->base == 0) plouf << '0';
    else plouf << (*n)->mantissa << ((*n)->base == 2 ? 'b' : 'e') << (*n)->exponent;
  else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "-+-*/";
    if (o->ops.size() == 1)
      plouf << '(' << op[o->type] << " r" << display(o->ops[0]) << ")%R";
    else
      plouf << "(r" << display(o->ops[0]) << ' ' << op[o->type] << " r" << display(o->ops[1]) << ")%R";
  } else if (rounded_real const *rr = boost::get< rounded_real const >(r))
    plouf << "roundingTODO r" << display(rr->rounded);
  else assert(false);
  plouf << ".\n";
  return r_id;
}

typedef std::map< std::string, int > property_map; // (not so) bastard way of doing it
static property_map displayed_properties;

int display(property const &p) {
  std::stringstream s;
  std::string name;
  if (ast_ident const *v = p.real->get_variable()) {
    name = '_' + v->name;
    s << "I754s_in";
  } else {
    s << "IR_in";
    std::stringstream ss;
    ss << 'r' << display(p.real);
    name = ss.str();
  }
  s << " i" << display(p.bnd) << ' ' << name;
  std::string s_ = s.str();
  int p_id = map_finder(displayed_properties, s_);
  if (p_id < 0) return -p_id;
  std::cout << "Definition p" << p_id << " := " << s_ << ".\n";
  return p_id;
}

typedef std::map< node *, int > node_map;
static node_map displayed_nodes;

int display(node *n) {
  int n_id = map_finder(displayed_nodes, n);
  if (n_id < 0) return -n_id;
  static char const *const node_ids[] = { "HYPOTHESIS", "CONCLUSION", "THEOREM", "MODUS", "UNION", "OTHER" };
  auto_flush plouf;
  plouf << "Lemma l" << n_id << " : ";
  for(property_vect::const_iterator i = n->hyp.begin(), end = n->hyp.end(); i != end; ++i)
    plouf << 'p' << display(*i) << " -> ";
  int p_res = display(n->res);
  plouf << 'p' << p_res << ".\n";
  plouf << " intros";
  for(int i = 0, l = n->hyp.size(); i < l; ++i) plouf << " h" << i;
  plouf << '.';
  if (n->type == THEOREM) {
    node_theorem *t = static_cast< node_theorem * >(n);
    plouf << " unfold p" << p_res << ".\n apply " << t->name << " with";
    for(int i = 0, l = n->hyp.size(); i < l; ++i) plouf << " (" << i + 1 << " := h" << i << ')';
    //plouf << " (" << n->hyp.size() + 1 << " := a" << "TODO" << ')';
    plouf << ".\n compute. trivial.\nQed.\n";
  } else if (n->type == MODUS) {
    plouf << '\n';
    typedef std::map< ast_real const *, int > property_map;
    property_map pmap;
    int nb_hyps = 0;
    for(property_vect::const_iterator j = n->hyp.begin(), j_end = n->hyp.end(); j != j_end; ++j, ++nb_hyps)
      pmap.insert(std::make_pair(j->real, nb_hyps));
    for(node_vect::const_iterator i = ++n->pred.begin(), i_end = n->pred.end(); i != i_end; ++i, ++nb_hyps) {
      plouf << " assert (h" << nb_hyps << " : p" << display((*i)->res) << "). apply l" << display(*i) << '.';
      for(property_vect::const_iterator j = (*i)->hyp.begin(), j_end = (*i)->hyp.end(); j != j_end; ++j) {
        /*
        if (error_bound const *e = boost::get< error_bound const >(j->real)) {
          if (e->var->real == e->real) {
            plouf << " apply refl.";
            continue;
          }
        }
        */
        property_map::iterator pki = pmap.find(j->real);
        assert(pki != pmap.end());
        plouf << " exact h" << pki->second << '.';
      }
      pmap.insert(std::make_pair((*i)->res.real, nb_hyps));
      plouf << '\n';
    }
    node *m = n->pred[0];
    plouf << " apply l" << display(m) << '.';
    for(property_vect::const_iterator j = m->hyp.begin(), j_end = m->hyp.end(); j != j_end; ++j) {
      /*
      if (error_bound const *e = boost::get< error_bound const >(j->real)) {
        if (e->var->real == e->real) {
          plouf << " apply refl.";
          continue;
        }
      }
      */
      property_map::iterator pki = pmap.find(j->real);
      assert(pki != pmap.end());
      plouf << " exact h" << pki->second << '.';
    }
    plouf << "\nQed.\n";
  } else {
    plouf << node_ids[n->type];
    for(node_vect::const_iterator i = n->pred.begin(), end = n->pred.end(); i != end; ++i)
      plouf << " l" << display(*i);
    plouf << '\n';
  }
  return n_id;
}

int main() {
  yyparse();
  for(node_set::const_iterator i = conclusions.begin(), end = conclusions.end(); i != end; ++i) {
    graph_layer layer;
    property p = (*i)->res;
    if (!generate_scheme_tree((*i)->hyp, p.real)) continue;
    node *n = handle_proof((*i)->hyp, p);
    if (!n || n == triviality) continue;
    if (ast_ident const *v = p.real->get_variable())
      std::cout << v->name;
    else
      std::cout << "...";
    std::cout << " in " << p.bnd << '\n';
    layer.flatten();
    (*i)->insert_pred(n);
  }
  std::cout << "\n\n";
  for(node_set::const_iterator i = conclusions.begin(), end = conclusions.end(); i != end; ++i) {
    node_vect const &v = (*i)->pred;
    if (v.empty()) continue;
    display(v[0]);
  }
}
