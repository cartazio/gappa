#include <iostream>
#include <stack>
#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/dichotomy.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

extern int parameter_dichotomy_depth;
extern bool warning_dichotomy_failure;

struct splitter {
  virtual bool split(interval &) = 0;
  virtual bool next(interval &) = 0;
  virtual ~splitter() {}
  bool merge;
};

struct fixed_splitter: splitter {
  interval bnd;
  unsigned steps;
  fixed_splitter(interval const &i, unsigned nb): bnd(i), steps(nb) { merge = false; }
  virtual bool split(interval &) { return false; }
  virtual bool next(interval &);
};

bool fixed_splitter::next(interval &i) {
  if (steps == 0) return false;
  if (steps == 1) {
    i = bnd;
    steps = 0;
    return true;
  }
  std::pair< interval, interval > ii = ::split(bnd, 1. / steps--);
  i = ii.first;
  bnd = ii.second;
  return true;
}

typedef std::vector< interval > interval_vect;

struct point_splitter: splitter {
  interval bnd;
  interval_vect const &bnds;
  unsigned pos;
  point_splitter(interval const &i, interval_vect const *b): bnd(i), bnds(*b), pos(0) {}
  virtual bool split(interval &) { return false; }
  virtual bool next(interval &);
};

bool point_splitter::next(interval &i) {
  for(unsigned sz = bnds.size(); pos < sz;) {
    i = intersect(bnd, bnds[pos++]);
    if (is_empty(i)) break;
    return true;
  }
  return false;
}

struct best_splitter: splitter {
  std::stack< interval > stack;
  best_splitter(interval const &i);
  virtual bool split(interval &);
  virtual bool next(interval &);
};

best_splitter::best_splitter(interval const &i) {
  std::pair< interval, interval > ii = ::split(i);
  stack.push(ii.second);
  stack.push(ii.first);
  merge = true;
}

bool best_splitter::split(interval &i) {
  if (stack.size() >= (unsigned)parameter_dichotomy_depth) return false;
  std::pair< interval, interval > ii = ::split(i);
  i = ii.first;
  stack.push(ii.second);
  return true;
}

bool best_splitter::next(interval &i) {
  if (stack.empty()) return false;
  i = stack.top();
  stack.pop();
  return true;
}

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
  splitter *gen;
  graph_t *try_hypothesis(dichotomy_failure * = NULL) const;
  void try_graph(graph_t *);
  void dichotomize();
  dichotomy_node *generate_node(node *, property const &);
  void purge();
  dichotomy_helper(property_vect &v, property_tree const &g, dichotomy_sequence const &h, splitter *s)
    : tmp_hyp(v), depth(0), nb_ref(0), goals(g), hints(h), last_graph(NULL), gen(s) {}
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
  delete gen;
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
  if (gen->merge) {
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
  interval &h = tmp_hyp[0].bnd();
  interval bnd;
  bool b = gen->next(bnd);
  assert(b);
  dichotomy_failure exn;
  for(;;) {
    h = bnd;
    if (graph_t *g = try_hypothesis(&exn)) {
      try_graph(g);
      if (!gen->next(bnd)) {
        graphs.push_back(last_graph);
        last_graph = NULL;
        return;
      }
    } else if (!gen->split(bnd)) {
      exn.hyp = tmp_hyp[0];
      throw exn;
    }
  }
}

bool graph_t::dichotomize(property_tree const &goals, dichotomy_hint const &hint) {
  assert(top_graph == this);
  dichotomy_sequence hints;
  assert(hint.src.size() >= 1);
  dichotomy_var const &var = hint.src[0];
  if (hint.src.size() > 1) {
    dichotomy_hint h;
    h.dst = hint.dst;
    h.src = dvar_vect(hint.src.begin() + 1, hint.src.end());
    hints.push_back(h);
  }
  node *varn = find_proof(var.real);
  if (!varn) return false;
  property_vect hyp2;
  hyp2.push_back(varn->get_result());
  property_vect const &hyp = top_graph->get_hypotheses();
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
    if (i->real.real() != var.real) hyp2.push_back(*i);
  splitter *gen;
  property_tree new_goals = goals;
  if (var.splitter & 1)
    gen = new fixed_splitter(hyp2[0].bnd(), var.splitter / 2);
  else if (var.splitter)
    gen = new point_splitter(hyp2[0].bnd(), (interval_vect const *)var.splitter);
  else if (hint.dst.empty())
    gen = new fixed_splitter(hyp2[0].bnd(), 4);
  else {
    new_goals.restrict(hint.dst);
    if (new_goals.empty()) {
      std::cerr << "Warning: case split is not goal-driven anymore.\n";
      return false;
    }
    gen = new best_splitter(hyp2[0].bnd());
  }
  dichotomy_helper *h = new dichotomy_helper(hyp2, new_goals, hints, gen);
  try {
    h->dichotomize();
  } catch (dichotomy_failure const &e) {
    if (warning_dichotomy_failure) {
      property const &h = e.hyp;
      std::cerr << "Warning: when " << dump_real(h.real.real()) << " is in "
                << h.bnd() << ", ";
      ast_real const *dst = e.expected.real.real();
      if (!dst)
        std::cerr << "nothing is satisfied.\n";
      else if (is_defined(e.found))
        std::cerr << dump_real(dst) << " is in " << e.found
                  << " potentially outside of " << e.expected.bnd() << ".\n";
      else
        std::cerr << dump_real(dst) << " is not computable.\n";
    }
    delete h;
    return false;
  }
  bool only_contradictions = true;
  typedef std::set< predicated_real > preal_set;
  preal_set reals;
  for(graph_vect::const_iterator i = h->graphs.begin(), i_end = h->graphs.end(); i != i_end; ++i) {
    if ((*i)->contradiction) continue;
    only_contradictions = false;
    for(node_map::const_iterator j = (*i)->known_reals.begin(), j_end = (*i)->known_reals.end(); j != j_end; ++j)
      reals.insert(j->first);
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
  for(preal_set::const_iterator i = reals.begin(), end = reals.end(); i != end; ++i) {
    property p(*i);
    if (node *n = find_already_known(*i)) p = n->get_result();
    if (node *n = h->generate_node(varn, p)) try_real(n);
  }
  if (--h->nb_ref == 0) {
    delete h;
    if (warning_dichotomy_failure)
      std::cerr << "Warning: case splitting on " << dump_real(var.real) << " did not produce any usable result.\n";
    return false;
  }
  return true;
}

interval create_interval(ast_interval const &, bool = true);

unsigned long fill_splitter(unsigned long s, ast_number const *n) {
  static ast_number const *o;
  interval_vect *v = (interval_vect *)s;
  if (!v) {
    ast_interval i = { NULL, n };
    v = new interval_vect(1, create_interval(i));
  } else {
    ast_interval i = { o, n };
    v->push_back(create_interval(i));
  }
  o = n;
  return (unsigned long)v;
}
