#include <iostream>
#include <map>
#include <sstream>
#include "ast.hpp"
#include "basic_proof.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "numbers/float.hpp"
#include "numbers/interval_ext.hpp"
#include "numbers/real.hpp"

extern int yyparse(void);
extern node *generate_proof(property_vect const &hyp, property const &res);
extern node *triviality;
extern number_real lower(interval_real const &v);
extern number_real upper(interval_real const &v);
extern std::string get_real_split(number_real const &f, int &exp, bool &zero);
extern std::string get_float_split(number_real const &f, int &exp, bool &zero, interval_float_description const *desc);

struct node_theorem: node {
  char const *name;
  node_theorem(int nb, property const *h, property const &p, char const *n);
};

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

int display(number_real const &f, interval_float_description const *desc = NULL) {
  std::stringstream s;
  bool zero;
  int exp, zero_exp;
  s << '(';
  if (desc) {
    s << get_float_split(f, exp, zero, desc);
    zero_exp = desc->min_exp - desc->prec;
  } else {
    s << get_real_split(f, exp, zero);
    zero_exp = 0;
  }
  s << ") (" << (zero ? zero_exp : exp) << ')';
  std::string s_ = s.str();
  s << ' ' << desc;
  int f_id = map_finder(displayed_floats, s.str());
  if (f_id < 0) return -f_id;
  if (desc) {
    std::cout << // TODO
      "Definition f" << f_id << "a := Float " << s_ << ".\n"
      "Lemma f" << f_id << "b : Good_f754s f" << f_id << "a. compute. left. repeat split; discriminate. Qed.\n" // TODO
      "Definition f" << f_id << " := F754s f" << f_id << "a f" << f_id << "b.\n";
  } else
    std::cout << "Definition f" << f_id << " := Float " << s_ << ".\n";
  return f_id;
}

typedef std::map< std::string, int > interval_map; // (not so) bastard way of doing it
static interval_map displayed_intervals;

int display(interval const &i) {
  std::stringstream s;
  interval_real const &r = to_real(i);
  interval_float_description const *desc =
    i.desc == interval_real_desc ? NULL : reinterpret_cast< interval_float_description const * >(i.desc);
  s << 'f' << display(lower(r), desc) << " f" << display(upper(r), desc);
  std::string s_ = s.str();
  s << ' ' << desc;
  int i_id = map_finder(displayed_intervals, s.str());
  if (i_id < 0) return -i_id;
  std::cout << "Definition i" << i_id << " := ";
  if (desc)
    std::cout << "I754s " << s_; // TODO
  else
    std::cout << "makepairR " << s_;
  std::cout << ".\n";
  return i_id;
}

typedef std::map< ast_real const *, int > real_map;
static real_map displayed_reals;

int display(ast_real const *r) {
  int r_id = map_finder(displayed_reals, r);
  if (r_id < 0) return -r_id;
  auto_flush plouf;
  plouf << "Definition r" << r_id << " := ";
  if (variable *const *v = boost::get< variable *const >(r))
    plouf << '_' << (*v)->name->name;
  else if (ast_number *const *n = boost::get< ast_number *const >(r))
    if ((*n)->base == 0) plouf << '0';
    else plouf << (*n)->mantissa << ((*n)->base == 2 ? 'b' : 'e') << (*n)->exponent;
  else if (real_op const *o = boost::get< real_op const >(r)) {
    static char const op[] = "-+-*/";
    if (o->ops.size() == 1)
      plouf << '(' << op[o->type] << " r" << display(o->ops[0]) << ")%R";
    else
      plouf << "(r" << display(o->ops[0]) << ' ' << op[o->type] << " r" << display(o->ops[1]) << ")%R";
  } else assert(false);
  plouf << ".\n";
  return r_id;
}

typedef std::map< std::string, int > property_map; // (not so) bastard way of doing it
static property_map displayed_properties;

int display(property const &p) {
  std::stringstream s;
  std::string const &name = p.var->name->name;
  if (p.type == PROP_BND)
    s << "I754s_BND";
  else if (p.type == PROP_ABS || p.type == PROP_REL)
    s << "I754s_" << (p.type == PROP_ABS ? "ABS" : "REL") << " r" << display(p.real);
  else assert(false);
  s << " i" << display(p.bnd) << " _" << name;
  std::string s_ = s.str();
  int p_id = map_finder(displayed_properties, s_);
  if (p_id < 0) return -p_id;
  std::cout << "Definition p" << p_id << " := " << s_ << ".\n";
  return p_id;
}

namespace {

struct property_key {
  property_type type;
  variable *var;
  ast_real const *real; // only used for ABS and REL
  property_key(property const &p): type(p.type), var(p.var), real(p.type != PROP_BND ? p.real : NULL) {}
  bool operator<(property_key const &p) const {
    return type < p.type || (type == p.type && (var < p.var || (var == p.var && real < p.real)));
  }
  typedef std::map< property_key, int > map;
};

} // anonymous namespace

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
    plouf << " unfold p" << p_res << ".\n apply " << static_cast< node_theorem * >(n)->name << " with";
    for(int i = 0, l = n->hyp.size(); i < l; ++i) plouf << " (" << i + 1 << " := h" << i << ')';
    plouf << " (" << n->hyp.size() << " := a" << "TODO" << ").\n compute. trivial.\nQed.\n";
  } else if (n->type == MODUS) {
    plouf << '\n';
    property_key::map pmap;
    int nb_hyps = 0;
    for(property_vect::const_iterator j = n->hyp.begin(), j_end = n->hyp.end(); j != j_end; ++j, ++nb_hyps) {
      property_key pk = *j;
      pmap.insert(std::make_pair(pk, nb_hyps));
    }
    for(node_vect::const_iterator i = ++n->pred.begin(), i_end = n->pred.end(); i != i_end; ++i, ++nb_hyps) {
      plouf << " assert (h" << nb_hyps << " : p" << display((*i)->res) << "). apply l" << display(*i) << '.';
      for(property_vect::const_iterator j = (*i)->hyp.begin(), j_end = (*i)->hyp.end(); j != j_end; ++j) {
        if (j->type != PROP_BND && j->var->real == j->real)
          plouf << " apply refl.";
        else {
          property_key pk = *j;
          property_key::map::iterator pki = pmap.find(pk);
          assert(pki != pmap.end());
          plouf << " exact h" << pki->second << '.';
        }
      }
      property_key pk = (*i)->res;
      pmap.insert(std::make_pair(pk, nb_hyps));
      plouf << '\n';
    }
    node *m = n->pred[0];
    plouf << " apply l" << display(m) << '.';
    for(property_vect::const_iterator j = m->hyp.begin(), j_end = m->hyp.end(); j != j_end; ++j) {
      if (j->type != PROP_BND && j->var->real == j->real)
        plouf << " apply refl.";
      else {
        property_key pk = *j;
        property_key::map::iterator pki = pmap.find(pk);
        assert(pki != pmap.end());
        plouf << " exact h" << pki->second << '.';
      }
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
    node *n = generate_proof((*i)->hyp, (*i)->res);
    if (!n) continue;
    property const &p = n->res;
    std::string const &name = p.var->name->name;
    if (p.type == PROP_BND)
      std::cout << name;
    else if (p.type == PROP_ABS || p.type == PROP_REL)
      std::cout << (p.type == PROP_ABS ? "ABS(" : "REL(") << name << ", ...)";
    else assert(false);
    std::cout << " in " << p.bnd << std::endl;
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
