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
 public:
  graph_t *last_graph;
  dichotomy_node(property_vect &v, property const &p, node *n)
      : dependent_node(UNION), tmp_hyp(v), depth(0), res(p), last_graph(NULL) {
    insert_pred(n);
  }
  ~dichotomy_node();
  void dichotomize();
  bool add_graph(graph_t *);
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

bool dichotomy_node::add_graph(graph_t *g) {
  graphs.push_back(g);
  node *n = g->get_contradiction();
  if (!n) n = g->find_already_known(get_result().real);
  insert_pred(n);
  g->purge();
  return g->migrate();
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
  bool b = g0->populate();
  if (!b)
    if (node *n = g0->find_already_known(res.real))
      if (n->get_result().bnd() <= res.bnd())
        b = true;
  if (b) {
    last_graph = g0;
    delete g1;
    delete g2;
    return;
  }
  delete g0;
  bool recompute = add_graph(g1);
  if (recompute) {
    // now that g1 has been added and some of its nodes have moved, recompute g2
    tmp_hyp.replace_front(g2->get_hypotheses()[0]);
    delete g2;
    g2 = new graph_t(top_graph, tmp_hyp, g1->get_goals());
    if (!g2->populate()) {
      node *n = g2->find_already_known(res.real);
      assert(n->get_result().bnd() <= res.bnd());
    }
  }
  last_graph = g2;
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
  if (!g->populate()) {
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

struct dichotomy_scheme: proof_scheme {
  ast_real const *var;
  mutable bool in_dichotomy;
  dichotomy_scheme(ast_real const *v, ast_real const *r);
  virtual node *generate_proof(interval const &) const;
  virtual node *generate_proof() const { return NULL; }
  virtual preal_vect needed_reals() const;
};

dichotomy_scheme::dichotomy_scheme(ast_real const *v, ast_real const *r)
  : proof_scheme(r), var(v), in_dichotomy(false) {
  ast_real_vect reals(1, r);
  assert(reals[0]);
}

preal_vect dichotomy_scheme::needed_reals() const {
  return preal_vect(1, predicated_real(var, PRED_BND));
}

node *dichotomy_scheme::generate_proof(interval const &bnd) const {
  if (in_dichotomy) return NULL;
  node *varn = find_proof(var);
  if (!varn) return NULL;
  in_dichotomy = true;
  property_vect hyp2;
  hyp2.push_back(varn->get_result());
  property_vect const &hyp = top_graph->get_hypotheses();
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
    if (i->real.real() != var) hyp2.push_back(*i);
  property_vect goals;
  goals.push_back(property(real, bnd));
  graph_t *g = new graph_t(top_graph, hyp, goals);
  graph_loader loader(g);
  dichotomy_node *n = new dichotomy_node(hyp2, property(real, bnd), varn);
  try {
    n->dichotomize();
    n->add_graph(n->last_graph);
    n->last_graph = NULL;
    ++n->nb_good;
    g->purge();
    g->flatten();
    --n->nb_good;
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
  delete g;
  in_dichotomy = false;
  return n;
}

struct dichotomy_factory: scheme_factory {
  ast_real const *dst, *var;
  dichotomy_factory(ast_real const *q1, ast_real const *q2): dst(q1), var(q2) {}
  virtual proof_scheme *operator()(predicated_real const &) const;
};

proof_scheme *dichotomy_factory::operator()(predicated_real const &r) const {
  if (r.pred() != PRED_BND || r.real() != dst) return NULL;
  return new dichotomy_scheme(var, dst);
}

void register_user_dichotomy(ast_real const *r1, ast_real const *r2) {
  scheme_register dummy(new dichotomy_factory(r1, r2));
}
