/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

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
extern bool detailed_io;

/**
 * Abstract generator of sub-intervals when performing a dichotomy.
 */
struct splitter
{
  /**
   * Splits the current interval and returns it in @a bnd.
   * @param bnd output interval.
   * @param iter_max amount of work to perform on the output interval.
   * @return false if the interval cannot be split anymore.
   */
  virtual bool split(interval &bnd, int &iter_max, bool &remove_left, bool &remove_right)
  { (void)&bnd; (void)&iter_max; (void)&remove_left; (void)&remove_right; return false; }
  /**
   * Returns the next interval in @a bnd.
   * @param bnd output interval.
   * @param iter_max amount of work to perform on the output interval.
   * @return false if all the intervals have been handled.
   */
  virtual bool next(interval &bnd, int &iter_max, bool &remove_left, bool &remove_right) = 0;
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
  int pos;       /**< Number of sub-intervals already handled. */
  int nb;        /**< Total number of sub-intervals. */
  int iter_max;  /**< Amount of work to perform on each sub-interval. */
  fixed_splitter(interval const &i, int n, int max)
    : bnd(i), left(i), pos(0), nb(n), iter_max(max / n) {}
  virtual bool next(interval &, int &, bool &, bool &);
};

/**
 * Splits the whole interval into two parts at ratio #pos / #nb.
 * Returns the sub-interval that has yet to be handled in the #left part.
 */
bool fixed_splitter::next(interval &i, int &max, bool &remove_left, bool &remove_right)
{
  if (pos++ == nb) return false;
  max = iter_max;
  if (pos == nb)
  {
    i = left;
    return true;
  }
  std::pair< interval, interval > ii = ::split(bnd, (double)pos / nb);
  i = intersect(left, ii.first);
  left = ii.second;
  remove_left = pos > 1;
  remove_right = false;
  return true;
}

typedef std::vector<split_point> number_vect;

/**
 * Generator of user-specified sub-intervals.
 */
struct point_splitter: splitter
{
  interval bnd;  /**< Whole interval. */
  number_vect const &bnds; /**< Sets of user-specified points. */
  int pos;       /**< Number of user points already handled. */
  int iter_max;  /**< Amount of work to perform on each sub-interval. */
  point_splitter(interval const &i, number_vect const *b, int max)
    : bnd(i), bnds(*b), pos(-1), iter_max(max / bnds.size()) {}
  virtual bool next(interval &, int &, bool &, bool &);
};

/**
 * Iteratively increments #pos until an intersection between #bnd and the user-specified intervals is found.
 * Returns this intersection.
 */
bool point_splitter::next(interval &i, int &max, bool &remove_left, bool &remove_right)
{
  max = iter_max;
  for(int sz = bnds.size(); pos++ < sz;)
  {
    i = intersect(bnd, interval(pos == 0  ? number::neg_inf : bnds[pos - 1].pt,
                                pos == sz ? number::pos_inf : bnds[pos].pt));
    if (is_empty(i) || is_singleton(i)) continue;
    remove_left = pos > 0 && bnds[pos - 1].inleft && lower(i) > lower(bnd);
    remove_right = pos < sz && !bnds[pos].inleft && upper(i) < upper(bnd);
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
  int iter_max; /**< Amount of work to perform on the whole interval. */
  best_splitter(interval const &i, int);
  virtual bool split(interval &, int &, bool &, bool &);
  virtual bool next(interval &, int &, bool &, bool &);
  virtual bool merge() { return true; }
  int get_iter_max() const;
};

/**
 * Stores the whole interval @a i at the top of the stack (it will be skipped by the first call to #next)
 * and its two sub-intervals.
 */
best_splitter::best_splitter(interval const &i, int max)
  : iter_max(max)
{
  std::pair< interval, interval > ii = ::split(i);
  stack.push(std::make_pair(ii.second, 1));
  stack.push(std::make_pair(ii.first, 1));
  stack.push(std::make_pair(i, 0));
}

/**
 * Returns the amount of work to perform at the current depth.
 */
int best_splitter::get_iter_max() const
{
  int depth = stack.top().second;
  if (depth > 30) return 10000;
  int max = iter_max / (1 << depth);
  return max < 10000 ? 10000 : max;
}

/**
 * Splits the interval at the top of the stack. Replaces it by the right part.
 * Pushes the left part and returns it. Sets an increased depth to both parts.
 */
bool best_splitter::split(interval &i, int &max, bool &remove_left, bool &remove_right)
{
  std::pair< interval, int > &p = stack.top();
  if (p.second >= parameter_dichotomy_depth) return false;
  std::pair< interval, interval > ii = ::split(p.first);
  if (!(ii.first < p.first && ii.second < p.first)) return false;
  p.first = ii.second;
  ++p.second;
  i = ii.first;
  stack.push(std::make_pair(i, p.second));
  max = get_iter_max();
  remove_left = false;
  remove_right = true;
  return true;
}

/**
 * Pops the interval at the top of the stack and returns the next one.
 */
bool best_splitter::next(interval &i, int &max, bool &remove_left, bool &remove_right)
{
  stack.pop();
  if (stack.empty()) return false;
  i = stack.top().first;
  max = get_iter_max();
  remove_left = false;
  remove_right = stack.size() > 1;
  return true;
}

typedef std::pair< graph_t *, int > dicho_graph;
typedef std::vector< dicho_graph > graph_vect;

class dichotomy_node;

struct dichotomy_failure {
  property hyp;
  property expected;
  interval found;
};

struct dichotomy_helper
{
  graph_vect graphs;
  property_vect &tmp_hyp;
  int iter_max;
  int depth;
  unsigned nb_ref;
  property_tree const &goals, &targets;
  dichotomy_sequence const &hints;
  dicho_graph last_graph;
  splitter *gen;
  dicho_graph try_hypothesis(dichotomy_failure *, bool, bool) const;
  void try_graph(dicho_graph);
  void dichotomize();
  dichotomy_node *generate_node(node *, property const &);
  dichotomy_helper(property_vect &v, property_tree const &g,
    property_tree const &t, dichotomy_sequence const &h, splitter *s)
  : tmp_hyp(v), depth(0), nb_ref(0), goals(g), targets(t), hints(h),
    last_graph(dicho_graph(NULL, 0)), gen(s) {}
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
  virtual void enlarge(property const &p) { res = boundify(p, res); }
  virtual property maximal_for(node const *) const;
};

property dichotomy_node::maximal_for(node const *n) const {
  if (n == get_subproofs()[0]) return n->get_result();
  return res;
}

dichotomy_helper::~dichotomy_helper() {
  assert(nb_ref == 0);
  for(graph_vect::iterator i = graphs.begin(), end = graphs.end(); i != end; ++i)
    delete i->first;
  graphs.clear();
  delete last_graph.first;
  delete gen;
}

dichotomy_node::~dichotomy_node() {
  clean_dependencies();
  if (--helper->nb_ref == 0)
    delete helper;
}

extern bool goal_reduction;

dicho_graph dichotomy_helper::try_hypothesis(dichotomy_failure *exn,
  bool remove_left, bool remove_right) const
{
  graph_t *g = new graph_t(top_graph, tmp_hyp);

  property_tree current_goals = goals;
  if (goal_reduction && !current_goals.empty())
  {
    graph_loader loader(g);
    property p = tmp_hyp[0];
    if (current_goals.simplify(p) > 0) {
      found_it:
      node *n = create_theorem(0, NULL, p, "$LOGIC");
      g->set_contradiction(n);
      return dicho_graph(g, iter_max);
    }
    if (!current_goals.empty()) {
      number n = lower(tmp_hyp[0].bnd());
      p.bnd() = remove_left ? interval(number::neg_inf, n) : interval(n, number::pos_inf);
      if (current_goals.simplify(p, !remove_left) > 0) goto found_it;
    }
    if (!current_goals.empty()) {
      number n = upper(tmp_hyp[0].bnd());
      p.bnd() = remove_right ? interval(n, number::pos_inf) : interval(number::neg_inf, n);
      if (current_goals.simplify(p, !remove_right) > 0) goto found_it;
    }
  }

  g->populate(current_goals, targets, hints, iter_max);
  if (g->get_contradiction() ||
      (targets.empty() ? current_goals : targets).verify(g, exn ? &exn->expected : NULL))
    return dicho_graph(g, iter_max);
  if (exn && !exn->expected.null()) {
    graph_loader loader(g);
    if (node *n = find_proof(exn->expected.real))
      exn->found = n->get_result().bnd();
    exn->hyp = find_proof(tmp_hyp[0].real)->get_result();
  }
  delete g;
  return dicho_graph(NULL, 0);
}

void dichotomy_helper::try_graph(dicho_graph g2)
{
  dicho_graph g1 = last_graph;
  if (!g1.first)
  {
    last_graph = g2;
    return;
  }
  if (gen->merge())
  {
    property p(g1.first->get_hypotheses()[0]);
    p.bnd() = interval(lower(p.bnd()), upper(g2.first->get_hypotheses()[0].bnd()));
    tmp_hyp[0] = p;
    iter_max = g1.second + g2.second;
    dicho_graph g = try_hypothesis(NULL, graphs.empty(), false);
    if (g.first)
    {
      // joined graph was successful, keep it as the last graph instead of g1 and g2
      delete g1.first;
      delete g2.first;
      last_graph = g;
      return;
    }
  }
  // validate g1 and keep g2 as the last graph
  graphs.push_back(g1);
  last_graph = g2;
}

dichotomy_node *dichotomy_helper::generate_node(node *varn, property const &p)
{
  property q;
  bool found_one = false;
  for (graph_vect::const_iterator i = graphs.begin(), end = graphs.end(); i != end; ++i)
  {
    graph_t *g = i->first;
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
  for (graph_vect::const_iterator i = graphs.begin(), end = graphs.end(); i != end; ++i)
  {
    graph_t *g = i->first;
    if (node *m = g->get_contradiction()) n->insert_pred(m); 
    else n->insert_pred(g->find_already_known(p.real));
  }
  return n;
}

void dichotomy_helper::dichotomize() {
  interval &h = tmp_hyp[0].bnd();
  interval bnd;
  bool rleft, rright;
  bool b = gen->next(bnd, iter_max, rleft, rright);
  assert(b && !rleft);
  dichotomy_failure exn;
  for (;;)
  {
    h = bnd;
    exn.hyp = tmp_hyp[0];
    dicho_graph g = try_hypothesis(&exn, rleft, rright);
    if (g.first)
    {
      try_graph(g);
      bool old_rright = rright;
      if (!gen->next(bnd, iter_max, rleft, rright))
      {
        graphs.push_back(last_graph);
        last_graph = dicho_graph(NULL, 0);
        (void)&old_rright;
        assert(!old_rright);
        return;
      }
    }
    else if (is_singleton(exn.hyp.bnd()) || !gen->split(bnd, iter_max, rleft, rright))
    {
      throw exn;
    }
  }
}

/**
 * Applies a ::dichotomy_hint.
 * @param goals subset of the user goal that drives the bisection.
 */
void graph_t::dichotomize(property_tree const &goals, dichotomy_hint const &hint, int iter_max)
{
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
    return;
  }
  property_vect hyp2;
  hyp2.push_back(varn->get_result());
  property_vect const &hyp = top_graph->get_hypotheses();
  for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i)
    if (i->real.real() != var.real) hyp2.push_back(*i);
  splitter *gen;
  property_tree targets;
  if (var.splitter & 1)
    gen = new fixed_splitter(hyp2[0].bnd(), var.splitter / 2, iter_max);
  else if (var.splitter)
    gen = new point_splitter(hyp2[0].bnd(), (number_vect const *)var.splitter, iter_max);
  else if (hint.dst.empty())
    gen = new fixed_splitter(hyp2[0].bnd(), 4, iter_max);
  else {
    targets = hint.dst;
    targets.fill_undefined(goals);
    if (targets.empty()) {
      if (warning_dichotomy_failure)
        std::cerr << "Warning: case split on " << dump_real(var.real)
                  << " is not goal-driven anymore.\n";
      return;
    }
    gen = new best_splitter(hyp2[0].bnd(), iter_max);
  }
  dichotomy_helper *h = new dichotomy_helper(hyp2, goals, targets, hints, gen);
  try {
    h->dichotomize();
  } catch (dichotomy_failure const &e) {
    if (warning_dichotomy_failure) {
      property const &h = e.hyp;
      change_io_format dummy(IO_FULL);
      std::cerr << "Warning: when " << dump_real_short(h.real) << " is in "
                << h.bnd() << ", ";
      predicated_real const &dst = e.expected.real;
      if (dst.null())
        std::cerr << "nothing is satisfied.\n";
      else if (is_defined(e.found))
        std::cerr << dump_real_short(dst) << " is in " << e.found
                  << " potentially outside of " << e.expected.bnd() << ".\n";
      else
        std::cerr << dump_real_short(dst) << " is not computable.\n";
    }
    delete h;
    return;
  }
  bool only_contradictions = true;
  typedef std::set< predicated_real > preal_set;
  preal_set reals;
  for (graph_vect::const_iterator i = h->graphs.begin(), i_end = h->graphs.end(); i != i_end; ++i)
  {
    graph_t *g = i->first;
    if (g->contradiction) continue;
    only_contradictions = false;
    for (node_map::const_iterator j = g->known_reals.begin(),
         j_end = g->known_reals.end(); j != j_end; ++j)
      reals.insert(j->first);
    break;
  }
  assert(!contradiction);
  if (only_contradictions) {
    dichotomy_node *n = new dichotomy_node(property(), h);
    n->insert_pred(varn);
    for(graph_vect::const_iterator i = h->graphs.begin(), end = h->graphs.end(); i != end; ++i)
      n->insert_pred(i->first->get_contradiction());
    set_contradiction(n);
    return;
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
    return;
  }
  for(graph_vect::const_iterator i = h->graphs.begin(), i_end = h->graphs.end(); i != i_end; ++i)
    i->first->purge();
}

interval create_interval(ast_number const *, ast_number const * = NULL, bool = true);

unsigned long fill_splitter(unsigned long s, ast_number const *n) {
  number_vect *v = (number_vect *)s;
  number m = lower(create_interval(n));
  split_point mb(m, true);
  if (!v) v = new number_vect(1, mb);
  else v->push_back(mb);
  return (unsigned long)v;
}

unsigned long fill_splitter(unsigned long s, split_point const &m)
{
  number_vect *v = (number_vect *)s;
  if (!v) v = new number_vect(1, m);
  else v->push_back(m);
  return (unsigned long)v;
}
