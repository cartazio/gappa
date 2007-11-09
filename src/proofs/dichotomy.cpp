#include <algorithm>
#include <iostream>
#include <stack>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "parser/ast.hpp"
#include "proofs/dichotomy.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"
#include "proofs/updater.hpp"

extern int parameter_dichotomy_depth;
extern bool warning_dichotomy_failure;

/**
 * Abstract generator of sub-intervals when performing a dichotomy.
 */
struct splitter
{
  /**
   * Splits the current interval and returns it in @a bnd.
   * @param bnd output interval.
   * @return false if the interval cannot be split anymore.
   */
  virtual bool split(interval &bnd)
  { (void)&bnd; return false; }
  /**
   * Returns the next interval in @a bnd.
   * @param bnd output interval.
   * @return false if all the intervals have been handled.
   */
  virtual bool next(interval &bnd) = 0;
  virtual ~splitter() {}
  /**
   * Indicates whether intervals should be merged afterwards.
   * @return false by default.
   */
  virtual bool merge()
  { return false; }
};

/**
 * Generator of equally-wide sub-intervals.
 */
struct fixed_splitter: splitter
{
  interval bnd;  /**< Whole interval. */
  interval left; /**< Already handled part of the whole interval. */
  unsigned pos;  /**< Number of sub-intervals already handled. */
  unsigned nb;   /**< Total number of sub-intervals. */
  fixed_splitter(interval const &i, unsigned n)
    : bnd(i), left(i), pos(0), nb(n) {}
  virtual bool next(interval &);
};

/**
 * Splits the whole interval into two parts at ratio #pos / #nb.
 * Returns the sub-interval that has yet to be handled in the #left part.
 */
bool fixed_splitter::next(interval &i)
{
  if (pos++ == nb) return false;
  if (pos == nb)
  {
    i = left;
    return true;
  }
  std::pair< interval, interval > ii = ::split(bnd, (double)pos / nb);
  i = intersect(left, ii.first);
  left = ii.second;
  return true;
}

typedef std::vector< number > number_vect;

/**
 * Generator of user-specified sub-intervals.
 */
struct point_splitter: splitter
{
  interval bnd; /**< Whole interval. */
  number_vect const &bnds; /**< Sets of user-specified points. */
  int pos; /**< Number of user points already handled. */
  point_splitter(interval const &i, number_vect const *b)
    : bnd(i), bnds(*b), pos(-1) {}
  virtual bool next(interval &);
};

/**
 * Iteratively increments #pos until an intersection between #bnd and the user-specified intervals is found.
 * Returns this intersection.
 */
bool point_splitter::next(interval &i)
{
  for(int sz = bnds.size(); pos++ < sz;)
  {
    i = intersect(bnd, interval(pos == 0  ? number::neg_inf : bnds[pos - 1],
                                pos == sz ? number::pos_inf : bnds[pos]));
    if (is_empty(i)) continue;
    return true;
  }
  return false;
}

/**
 * Generator of sub-intervals based on dichotomy. A merge of the sub-intervals is performed at the end.
 */
struct best_splitter: splitter
{
  /**
   * Stack of sub-intervals not handled yet and their depth in the dichotomy tree.
   * Top of the stack is the currently handled interval.
   */
  std::stack< std::pair< interval, int > > stack;
  best_splitter(interval const &i);
  virtual bool split(interval &);
  virtual bool next(interval &);
  virtual bool merge() { return true; }
};

/**
 * Stores the whole interval @a i at the top of the stack (it will be skipped by the first call to #next)
 * and its two sub-intervals.
 */
best_splitter::best_splitter(interval const &i)
{
  std::pair< interval, interval > ii = ::split(i);
  stack.push(std::make_pair(ii.second, 1));
  stack.push(std::make_pair(ii.first, 1));
  stack.push(std::make_pair(i, 0));
}

/**
 * Splits the interval at the top of the stack. Replaces it by the right part.
 * Pushes the left part and returns it. Sets an increased depth to both parts.
 */
bool best_splitter::split(interval &i)
{
  std::pair< interval, int > &p = stack.top();
  if (p.second >= parameter_dichotomy_depth) return false;
  std::pair< interval, interval > ii = ::split(p.first);
  if (!(ii.first < p.first && ii.second < p.first)) return false;
  p.first = ii.second;
  ++p.second;
  i = ii.first;
  stack.push(std::make_pair(i, p.second));
  return true;
}

/**
 * Pops the interval at the top of the stack and returns the next one.
 */
bool best_splitter::next(interval &i)
{
  stack.pop();
  if (stack.empty()) return false;
  i = stack.top().first;
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
  virtual void enlarge(property const &p) { res = boundify(p, res); }
  virtual property maximal_for(node const *) const;
};

property dichotomy_node::maximal_for(node const *n) const {
  if (n == get_subproofs()[0]) return n->get_result();
  return res;
}

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
  if (gen->merge()) {
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

/**
 * Applies a ::dichotomy_hint.
 * @param goals subset of the user goal that drives the bisection.
 * @return true if a contradiction is found.
 */
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
  if (!varn) {
    if (warning_dichotomy_failure)
      std::cerr << "Warning: case split on " << dump_real(var.real)
                << " has no range to split.\n";
    return false;
  }
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
    gen = new point_splitter(hyp2[0].bnd(), (number_vect const *)var.splitter);
  else if (hint.dst.empty())
    gen = new fixed_splitter(hyp2[0].bnd(), 4);
  else {
    new_goals.restrict(hint.dst);
    if (new_goals.empty()) {
      if (warning_dichotomy_failure)
        std::cerr << "Warning: case split on " << dump_real(var.real)
                  << " is not goal-driven anymore.\n";
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
      std::cerr << "Warning: case split on " << dump_real(var.real)
                << " has not produced any interesting new result.\n";
    return false;
  }
  for(graph_vect::const_iterator i = h->graphs.begin(), i_end = h->graphs.end(); i != i_end; ++i)
    (*i)->purge();
  return true;
}

interval create_interval(ast_number const *, ast_number const * = NULL, bool = true);

unsigned long fill_splitter(unsigned long s, ast_number const *n) {
  number_vect *v = (number_vect *)s;
  number m = lower(create_interval(n));
  if (!v) v = new number_vect(1, m);
  else v->push_back(m);
  return (unsigned long)v;
}
