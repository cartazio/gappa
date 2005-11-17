#include <iostream>
#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/dichotomy.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

extern int parameter_dichotomy_depth;
extern bool warning_dichotomy_failure;

typedef std::vector< graph_t * > graph_vect;

class dichotomy_node;

struct dichotomy_failure {
  property hyp;
  property expected;
  interval found;
};

struct dichotomy_helper {
  graph_vect graphs;
  property_vect &tmp_hyp;
  int depth;
  unsigned nb_ref;
  property_tree const &goals;
  dichotomy_sequence const &hints;
  graph_t *last_graph;
  graph_t *try_hypothesis(dichotomy_failure * = NULL) const;
  void try_graph(graph_t *);
  void dichotomize();
  dichotomy_node *generate_node(node *, property const &);
  void purge();
  dichotomy_helper(property_vect &v, property_tree const &g, dichotomy_sequence const &h)
    : tmp_hyp(v), depth(0), nb_ref(0), goals(g), hints(h), last_graph(NULL) {}
  ~dichotomy_helper();
};

class dichotomy_node: public dependent_node {
  property res;
  dichotomy_helper *helper;
 public:
  dichotomy_node(property const &p, dichotomy_helper *h)
    : dependent_node(UNION), res(p), helper(h) { ++h->nb_ref; }
  ~dichotomy_node();
  virtual property const &get_result() const { return res; }
  using dependent_node::insert_pred;
  virtual long get_hyps() const;
};

static char const *all_one() {
  static char v[256];
  for(int i = 0; i < 256; ++i) v[i] = -1;
  return v;
}

long dichotomy_node::get_hyps() const {
  static char const *s = all_one();
  unsigned nb = graph->get_hypotheses().size();
  if (nb <= sizeof(long) * 8) return -1;
  assert(graph->get_hypotheses().size() <= 256 * 8);
  return reinterpret_cast< long >(s);
}

dichotomy_helper::~dichotomy_helper() {
  assert(nb_ref == 0);
  for(graph_vect::iterator i = graphs.begin(), end = graphs.end(); i != end; ++i)
    delete *i;
  graphs.clear();
  delete last_graph;
}

dichotomy_node::~dichotomy_node() {
  clean_dependencies();
  if (--helper->nb_ref == 0)
    delete helper;
}

graph_t *dichotomy_helper::try_hypothesis(dichotomy_failure *exn) const {
  graph_t *g = new graph_t(top_graph, tmp_hyp);
  if (g->populate(goals, hints) || goals.verify(g, exn ? &exn->expected : NULL)) return g;
  if (exn && !exn->expected.null()) {
    graph_loader loader(g);
    if (node *n = find_proof(exn->expected.real))
      exn->found = n->get_result().bnd();
  }
  delete g;
  return NULL;
}

void dichotomy_helper::try_graph(graph_t *g2) {
  graph_t *g1 = last_graph;
  if (!g1) {
    last_graph = g2;
    return;
  }
  if (!goals.empty()) { // try joining only if we have constraints
    property p(g1->get_hypotheses()[0]);
    p.bnd() = interval(lower(p.bnd()), upper(g2->get_hypotheses()[0].bnd()));
    tmp_hyp[0] = p;
    if (graph_t *g = try_hypothesis()) {
      // joined graph was successful, keep it as the last graph instead of g1 and g2
      delete g1;
      delete g2;
      last_graph = g;
      return;
    }
  }
  // validate g1 and keep g2 as the last graph
  graphs.push_back(g1);
  last_graph = g2;
}

dichotomy_node *dichotomy_helper::generate_node(node *varn, property const &p) {
  property q;
  bool found_one = false;
  for(graph_vect::const_iterator i = graphs.begin(), end = graphs.end(); i != end; ++i) {
    graph_t *g = *i;
    if (g->get_contradiction()) continue;
    node *n = g->find_already_known(p.real);
    if (!n) return NULL;
    property const &r = n->get_result();
    if (!r.implies(p)) return NULL;
    if (!found_one) {
      q = r;
      found_one = true;
    } else
      q.hull(r);
  }
  assert(found_one && q.implies(p));
  if (!q.strict_implies(p)) return NULL;
  dichotomy_node *n = new dichotomy_node(q, this);
  n->insert_pred(varn);
  for(graph_vect::const_iterator i = graphs.begin(), end = graphs.end(); i != end; ++i) {
    graph_t *g = *i;
    if (node *m = g->get_contradiction()) n->insert_pred(m); 
    else n->insert_pred((*i)->find_already_known(p.real));
  }
  return n;
}

void dichotomy_helper::dichotomize() {
  property const &h = tmp_hyp[0];
  if (depth != 0) {
    dichotomy_failure exn;
    if (graph_t *g = try_hypothesis(&exn)) {
      try_graph(g);
      return;
    }
    if (depth >= parameter_dichotomy_depth) {
      exn.hyp = h;
      throw exn;
    }
  }
  std::pair< interval, interval > ii = split(h.bnd());
  ++depth;
  tmp_hyp[0] = property(h.real, ii.first);
  dichotomize();
  tmp_hyp[0] = property(h.real, ii.second);
  dichotomize();
  --depth;
}

bool graph_t::dichotomize(property_tree const &goals, dichotomy_hint const &hint) {
  assert(top_graph == this);
  dichotomy_sequence hints;
  assert(hint.src.size() >= 1);
  ast_real const *var = hint.src[0];
  if (hint.src.size() > 1) {
    dichotomy_hint h;
    h.dst = hint.dst;
    h.src = ast_real_vect(hint.src.begin() + 1, hint.src.end());
    hints.push_back(h);
  }
  node *varn = find_proof(var);
  if (!varn) return false;
  property_vect hyp2;
  hyp2.push_back(varn->get_result());
  property_vect const &hyp = top_graph->get_hypotheses();
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
    if (i->real.real() != var) hyp2.push_back(*i);
  property_tree new_goals = goals;
  new_goals.restrict(hint.dst);
  dichotomy_helper *h = new dichotomy_helper(hyp2, new_goals, hints);
  try {
    h->dichotomize();
  } catch (dichotomy_failure const &e) {
    if (warning_dichotomy_failure) {
      property const &h = e.hyp;
      std::cerr << "Warning: when " << dump_real(h.real.real()) << " is in "
                << h.bnd() << ", " << dump_real(e.expected.real.real());
      if (is_defined(e.found))
        std::cerr << " is in " << e.found << " potentially outside of "
                  << e.expected.bnd() << '\n';
      else
        std::cerr << " is not computable\n";
    }
    delete h;
    return false;
  }
  h->graphs.push_back(h->last_graph);
  h->last_graph = NULL;
  bool only_contradictions = true;
  preal_vect reals;
  for(graph_vect::const_iterator i = h->graphs.begin(), i_end = h->graphs.end(); i != i_end; ++i) {
    if ((*i)->contradiction) continue;
    only_contradictions = false;
    for(node_map::const_iterator j = known_reals.begin(), j_end = known_reals.end(); j != j_end; ++j)
      reals.push_back(j->first);
    break;
  }
  assert(!contradiction);
  if (only_contradictions) {
    dichotomy_node *n = new dichotomy_node(property(), h);
    n->insert_pred(varn);
    for(graph_vect::const_iterator i = h->graphs.begin(), end = h->graphs.end(); i != end; ++i)
      n->insert_pred((*i)->get_contradiction());
    set_contradiction(n);
    return true;
  }
  ++h->nb_ref;
  for(preal_vect::const_iterator i = reals.begin(), end = reals.end(); i != end; ++i) {
    property p(*i);
    if (node *n = find_already_known(*i)) p = n->get_result();
    if (node *n = h->generate_node(varn, p)) try_real(n);
  }
  if (--h->nb_ref == 0) {
    delete h;
    if (warning_dichotomy_failure)
      std::cerr << "Warning: case splitting on " << dump_real(var) << " did not produce any usable result.\n";
    return false;
  }
  return true;
}
