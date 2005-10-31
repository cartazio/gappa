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

class dichotomy_node: public dependent_node {
  graph_vect graphs;
  property_vect &tmp_hyp;
  int depth;
  property res;
  dichotomy_sequence const &hints;
 public:
  graph_t *last_graph;
  dichotomy_node(property_vect &v, property const &p, node *n, dichotomy_sequence const &h)
      : dependent_node(UNION), tmp_hyp(v), depth(0), res(p), hints(h), last_graph(NULL) {
    insert_pred(n);
  }
  ~dichotomy_node();
  void dichotomize();
  void add_graph(graph_t *);
  void try_graph(graph_t *);
  virtual property const &get_result() const { return res; }
  virtual property_vect const &get_hypotheses() const { return graph->get_hypotheses(); }
};

dichotomy_node::~dichotomy_node() {
  clean_dependencies();
  for(graph_vect::iterator i = graphs.begin(), end = graphs.end(); i != end; ++i)
    delete *i;
  graphs.clear();
  delete last_graph;
  last_graph = NULL;
}

void dichotomy_node::add_graph(graph_t *g) {
  graphs.push_back(g);
  node *n = g->get_contradiction();
  if (!n) n = g->find_already_known(get_result().real);
  insert_pred(n);
  g->purge();
}

void dichotomy_node::try_graph(graph_t *g2) {
  graph_t *g1 = last_graph;
  if (!g1) {
    last_graph = g2;
    return;
  }
  property p(g1->get_hypotheses()[0]);
  p.bnd() = interval(lower(p.bnd()), upper(g2->get_hypotheses()[0].bnd()));
  tmp_hyp.replace_front(p);
  property const &res = get_result();
  graph_t *g0 = new graph_t(top_graph, tmp_hyp, g1->get_goals());
  bool b = g0->populate(hints);
  if (!b)
    if (node *n = g0->find_already_known(res.real))
      if (n->get_result().bnd() <= res.bnd())
        b = true;
  if (b) {
    // graph g0 was successful, keep it as the last graph instead of g1 and g2
    last_graph = g0;
    delete g1;
    delete g2;
  } else {
    // graph g0 was a failure, validate g1 and keep g2 as the last graph
    delete g0;
    add_graph(g1);
    last_graph = g2;
  }
}

struct dichotomy_failure {
  property hyp;
  property res;
  interval bnd;
  dichotomy_failure(property const &h, property const &r, interval const &b): hyp(h), res(r), bnd(b) {}
};

void dichotomy_node::dichotomize() {
  property const &res = get_result();
  interval bnd;
  graph_t *g = new graph_t(top_graph, tmp_hyp, top_graph->get_goals());
  bool good = true;
  if (!g->populate(hints)) {
    if (node *n = g->find_already_known(res.real)) {
      bnd = n->get_result().bnd();
      if (!(bnd <= res.bnd())) good = false;
    } else good = false;
  }
  if (good) {
    try_graph(g);
    return;
  }
  property const &h = tmp_hyp[0];
  node *n = g->find_already_known(h.real);
  assert(n);
  interval i = n->get_result().bnd();
  delete g;
  if (!is_defined(i) || is_singleton(i)) throw dichotomy_failure(h, res, bnd);
  std::pair< interval, interval > ii = split(h.bnd());
  if (++depth > parameter_dichotomy_depth) throw dichotomy_failure(h, res, bnd);
  tmp_hyp.replace_front(property(h.real, ii.first));
  dichotomize();
  tmp_hyp.replace_front(property(h.real, ii.second));
  dichotomize();
  --depth;
}

void graph_t::dichotomize(dichotomy_hint const &hint) {
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
  graph_t *g = new graph_t(top_graph, hyp, new_goals);
  dichotomy_node *n = NULL;
  try {
    graph_loader loader(g);
    n = new dichotomy_node(hyp2, new_goals[0], varn, hints);
    n->dichotomize();
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
    delete n;
    n = NULL;
  }
  if (n) {
    n->add_graph(n->last_graph);
    n->last_graph = NULL;
    ++n->nb_good;
    g->purge();
    g->flatten();
    --n->nb_good;
    try_real(n);
  }
  delete g;
}
