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


struct dichotomy_helper {
  graph_vect graphs;
  property_vect &tmp_hyp;
  int depth;
  unsigned nb_ref;
  property res;
  dichotomy_sequence const &hints;
  graph_t *last_graph;
  graph_t *try_hypothesis(interval *) const;
  void try_graph(graph_t *);
  void dichotomize();
  dichotomy_node *generate_node(node *, property const &);
  void purge();
  dichotomy_helper(property_vect &v, property const &p, dichotomy_sequence const &h)
    : tmp_hyp(v), depth(0), nb_ref(0), res(p), hints(h), last_graph(NULL) {}
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
  virtual property_vect const &get_hypotheses() const { return graph->get_hypotheses(); }
  using dependent_node::insert_pred;
};

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

graph_t *dichotomy_helper::try_hypothesis(interval *i) const {
  graph_t *g = new graph_t(top_graph, tmp_hyp, top_graph->get_goals());
  bool success = g->populate(hints);
  if (!success) // no contradiction
    if (node *n = g->find_already_known(res.real)) {
      interval const &bnd = n->get_result().bnd();
      if (bnd <= res.bnd()) success = true;
      if (i) *i = bnd;
    }
  if (!success) { // no contradiction and no node good enough
    delete g;
    return NULL;
  }
  return g;
}

void dichotomy_helper::try_graph(graph_t *g2) {
  graph_t *g1 = last_graph;
  if (!g1) {
    last_graph = g2;
    return;
  }
  property p(g1->get_hypotheses()[0]);
  p.bnd() = interval(lower(p.bnd()), upper(g2->get_hypotheses()[0].bnd()));
  tmp_hyp.replace_front(p);
  if (graph_t *g = try_hypothesis(NULL)) {
    // hull graph was successful, keep it as the last graph instead of g1 and g2
    delete g1;
    delete g2;
    last_graph = g;
  } else {
    // validate g1 and keep g2 as the last graph
    graphs.push_back(g1);
    last_graph = g2;
  }
}

dichotomy_node *dichotomy_helper::generate_node(node *varn, property const &p) {
  assert(p.real.pred() == PRED_BND);
  interval bnd;
  for(graph_vect::const_iterator i = graphs.begin(), end = graphs.end(); i != end; ++i) {
    graph_t *g = *i;
    if (g->get_contradiction()) continue;
    node *n = g->find_already_known(p.real);
    if (!n) return NULL;
    property const &res = n->get_result();
    if (!res.implies(p)) return NULL;
    interval const &b = res.bnd();
    if (!is_defined(bnd)) bnd = b;
    else bnd = hull(bnd, b);
  }
  assert(is_defined(bnd) && bnd <= p.bnd());
  if (!(bnd < p.bnd())) return NULL;
  dichotomy_node *n = new dichotomy_node(property(p.real, bnd), this);
  n->insert_pred(varn);
  for(graph_vect::const_iterator i = graphs.begin(), end = graphs.end(); i != end; ++i) {
    graph_t *g = *i;
    if (node *m = g->get_contradiction()) n->insert_pred(m); 
    else n->insert_pred((*i)->find_already_known(p.real));
  }
  return n;
}

struct dichotomy_failure {
  property hyp;
  property res;
  interval bnd;
  dichotomy_failure(property const &h, property const &r, interval const &b): hyp(h), res(r), bnd(b) {}
};

void dichotomy_helper::dichotomize() {
  property const &h = tmp_hyp[0];
  if (depth != 0) {
    interval bnd;
    if (graph_t *g = try_hypothesis(&bnd)) {
      try_graph(g);
      return;
    }
    if (depth >= parameter_dichotomy_depth) throw dichotomy_failure(h, res, bnd);
  }
  std::pair< interval, interval > ii = split(h.bnd());
  ++depth;
  tmp_hyp.replace_front(property(h.real, ii.first));
  dichotomize();
  tmp_hyp.replace_front(property(h.real, ii.second));
  dichotomize();
  --depth;
}

void graph_t::dichotomize(dichotomy_hint const &hint) {
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
  if (!varn) return;
  property_vect hyp2;
  hyp2.push_back(varn->get_result());
  property_vect const &hyp = top_graph->get_hypotheses();
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
    if (i->real.real() != var) hyp2.push_back(*i);
  assert(hint.dst.size() == 1);
  property_vect new_goals;
  for(property_vect::const_iterator i = goals.begin(), end = goals.end(); i != end; ++i)
    if (i->real.pred() == PRED_BND && i->real.real() == hint.dst[0])
      new_goals.push_back(*i);
  if (new_goals.size() != 1) return;
  dichotomy_helper *h = new dichotomy_helper(hyp2, new_goals[0], hints);
  try {
    h->dichotomize();
  } catch (dichotomy_failure const &e) {
    if (warning_dichotomy_failure) {
      property const &h = e.hyp;
      std::cerr << "Warning: when " << dump_real(h.real.real()) << " is in " << h.bnd() << ", ";
      property const &p = e.res;
      std::cerr << dump_real(p.real.real());
      if (is_defined(e.bnd))
        std::cerr << " is in " << e.bnd << " potentially outside of " << p.bnd() << '\n';
      else
        std::cerr << " is not computable\n";
    }
    delete h;
    return;
  }
  h->graphs.push_back(h->last_graph);
  h->last_graph = NULL;
  node *n = h->generate_node(varn, property(hint.dst[0]));
  try_real(n);
}
