#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/dichotomy.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

typedef std::vector< graph_t * > graph_vect;

class dichotomy_node: public dependent_node {
  graph_vect graphs;
  property_vect &tmp_hyp;
  int depth;
 public:
  graph_t *last_graph;
  dichotomy_node(property_vect &v, property const &p)
      : dependent_node(UNION, p), tmp_hyp(v), depth(0), last_graph(NULL) {
    hyp = v;
  }
  ~dichotomy_node();
  void dichotomize();
  bool add_graph(graph_t *);
  void try_graph(graph_t *);
  virtual void clean_dependencies();
};

void dichotomy_node::clean_dependencies() {
  dependent_node::clean_dependencies();
  for(graph_vect::iterator i = graphs.begin(), end = graphs.end(); i != end; ++i)
    delete *i;
  graphs.clear();
  delete last_graph;
  last_graph = NULL;
}

dichotomy_node::~dichotomy_node() {
  clean_dependencies();
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
  p.bnd = interval(lower(p.bnd), upper(g2->get_hypotheses()[0].bnd));
  tmp_hyp.replace_front(p);
  property const &res = get_result();
  graph_t *g0 = new graph_t(top_graph, tmp_hyp, g1->get_goals(), top_graph->helper, true);
  bool b = g0->populate();
  if (!b)
    if (node *n = g0->find_already_known(res.real))
      if (n->get_result().bnd <= res.bnd)
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
    g2 = new graph_t(top_graph, tmp_hyp, g1->get_goals(), top_graph->helper, true);
    if (!g2->populate()) {
      node *n = g2->find_already_known(res.real);
      assert(n->get_result().bnd <= res.bnd);
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
  graph_t *g = new graph_t(top_graph, tmp_hyp, top_graph->get_goals(), top_graph->helper, true);
  if (!g->populate()) {
    if (node *n = g->find_already_known(res.real)) {
      bnd = n->get_result().bnd;
      if (!(bnd <= res.bnd)) { delete g; g = NULL; }
    } else { delete g; g = NULL; }
  }
  if (g) {
    try_graph(g);
    return;
  }
  property const &h = tmp_hyp[0];
  if (rounded_real const *rr = boost::get< rounded_real const >(res.real)) {
    std::string dummy;
    interval i = rr->rounding->enforce(h.bnd, dummy);
    if (!is_defined(i) || is_singleton(i)) throw dichotomy_failure(h, res, bnd);
  }
  std::pair< interval, interval > ii = split(h.bnd);
  if (++depth > 100) throw dichotomy_failure(h, res, bnd);
  tmp_hyp.replace_front(property(h.real, ii.first));
  dichotomize();
  tmp_hyp.replace_front(property(h.real, ii.second));
  dichotomize();
  --depth;
}

struct dichotomy_scheme: proof_scheme {
  ast_real const *var;
  mutable node *dich;
  proof_helper *helper;
  dichotomy_scheme(ast_real const *v, ast_real const *r);
  ~dichotomy_scheme() { delete_proof_helper(helper); }
  virtual node *generate_proof(interval const &) const;
  virtual node *generate_proof() const { return dich; }
  virtual ast_real_vect needed_reals() const;
};

static bool no_dichotomy = false;

dichotomy_scheme::dichotomy_scheme(ast_real const *v, ast_real const *r)
  : proof_scheme(r), var(v), dich(NULL) {
  ast_real_vect reals(1, r);
  no_dichotomy = true;
  helper = generate_proof_helper(reals);
  no_dichotomy = false;
  assert(reals[0]);
}

ast_real_vect dichotomy_scheme::needed_reals() const {
  ast_real_vect res;
  //res.push_back(real);
  res.push_back(var);
  return res;
}

node *dichotomy_scheme::generate_proof(interval const &bnd) const {
  if (dich) return dich;
  node *varn = find_proof(var);
  if (!varn) return NULL;
  property_vect hyp2;
  hyp2.push_back(varn->get_result());
  property_vect const &hyp = top_graph->get_hypotheses();
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
    if (i->real != var) hyp2.push_back(*i);
  property_vect goals;
  goals.push_back(property(real, bnd));
  graph_t *g = new graph_t(top_graph, hyp, goals, helper, false);
  graph_loader loader(g);
  dichotomy_node *n = new dichotomy_node(hyp2, property(real, bnd));
  try {
    n->dichotomize();
    n->add_graph(n->last_graph);
    n->last_graph = NULL;
    dich = create_modus(n);
    g->purge(dich);
    g->flatten();
  } catch (dichotomy_failure e) { // BLI
    /*
    property const &h = e.hyp;
    std::cerr << "failure: when " << dump_real(h.real) << " is " << h.bnd << ", ";
    property const &p = e.res;
    std::cerr << dump_real(p.real);
    if (is_defined(e.bnd))
      std::cerr << " is in " << e.bnd << " potentially outside of " << p.bnd << '\n';
    else
      std::cerr << " is nowhere (?!)\n";
    */
    dich = NULL;
  }
  delete g;
  return dich;
}

struct dichotomy_factory: scheme_factory {
  ast_real const *dst, *var;
  dichotomy_factory(ast_real const *q1, ast_real const *q2): dst(q1), var(q2) {}
  virtual proof_scheme *operator()(ast_real const *) const;
};

proof_scheme *dichotomy_factory::operator()(ast_real const *r) const {
  if (no_dichotomy || r != dst) return NULL;
  return new dichotomy_scheme(var, dst);
}

void register_user_dichotomy(ast_real const *r1, ast_real const *r2) {
  scheme_register dummy(new dichotomy_factory(r1, r2));
}
