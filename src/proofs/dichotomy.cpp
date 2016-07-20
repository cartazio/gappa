/*
   Copyright (C) 2004 - 2015 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
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

struct backend;

extern int parameter_dichotomy_depth;
extern bool warning_dichotomy_failure;
extern bool detailed_io;
extern backend *proof_generator;

/**
 * Abstract generator of sub-intervals when performing a dichotomy.
 */
struct splitter
{
  /**
   * Splits the current interval and returns the splitting point in @a sp.
   * @param iter_max amount of work to perform on the output interval.
   * @return false if the interval cannot be split anymore.
   */
  virtual bool split(number &sp, int &iter_max)
  { return false; }
  /**
   * Returns the next splitting point.
   * @param iter_max amount of work to perform on the output interval.
   * @return false if all the intervals have been handled.
   */
  virtual number next(int &iter_max) = 0;
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
  int pos;       /**< Number of sub-intervals already handled. */
  int nb;        /**< Total number of sub-intervals. */
  int iter_max;  /**< Amount of work to perform on each sub-interval. */
  fixed_splitter(interval const &i, int n, int max)
    : bnd(i), pos(0), nb(n), iter_max(max / n)
  { assert(is_bounded(bnd)); }
  virtual number next(int &);
};

/**
 * Splits the whole interval into two parts at ratio #pos / #nb.
 * Returns the sub-interval that has yet to be handled in the #left part.
 */
number fixed_splitter::next(int &max)
{
  max = iter_max;
  if (++pos == nb) return number::pos_inf;
  std::pair< interval, interval > ii = ::split(bnd, (double)pos / nb);
  return upper(ii.first);
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
  virtual number next(int &);
};

/**
 * Iteratively increments #pos until an intersection between #bnd and the user-specified intervals is found.
 * Returns this intersection.
 */
number point_splitter::next(int &max)
{
  max = iter_max;
  for(int sz = bnds.size(); ++pos < sz;)
  {
    number res = bnds[pos].pt;
    if (res <= lower(bnd)) continue;
    if (pos > 0 && res == bnds[pos - 1].pt) continue;
    if (res < upper(bnd)) return res;
  }
  return number::pos_inf;
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
  virtual bool split(number &, int &);
  virtual number next(int &);
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
bool best_splitter::split(number &res, int &max)
{
  std::pair< interval, int > &p = stack.top();
  if (p.second >= parameter_dichotomy_depth) return false;
  std::pair< interval, interval > ii = ::split(p.first);
  if (!(ii.first < p.first && ii.second < p.first)) return false;
  p.first = ii.second;
  ++p.second;
  stack.push(std::make_pair(ii.first, p.second));
  res = upper(ii.first);
  max = get_iter_max();
  return true;
}

/**
 * Pops the interval at the top of the stack and returns the next one.
 */
number best_splitter::next(int &max)
{
  stack.pop();
  assert(!stack.empty());
  max = get_iter_max();
  if (stack.size() == 1) return number::pos_inf;
  return upper(stack.top().first);
}

typedef std::pair< graph_t *, int > dicho_graph;
typedef std::vector<graph_t *> graph_vect;

class dichotomy_node;

struct dichotomy_failure {
  property hyp;
  property expected;
  property found;
};

struct dichotomy_graphs
{
  graph_vect graphs;
  unsigned nb_ref;
  dichotomy_graphs(): nb_ref(0) {}
  ~dichotomy_graphs();
};

struct dichotomy_helper
{
  dichotomy_graphs *graphs;
  property tmp_hyp;
  int iter_max;
  int depth;
  property_tree const &targets;
  dichotomy_sequence const &hints;
  dicho_graph last_graph;
  splitter *gen;
  dicho_graph try_hypothesis(dichotomy_failure *) const;
  void try_graph(dicho_graph);
  void dichotomize();
  dichotomy_node *generate_node(property const &);
  dichotomy_helper(ast_real const *v, property_tree const &t,
    dichotomy_sequence const &h, splitter *s)
  : graphs(new dichotomy_graphs()), tmp_hyp(v), depth(0),
    targets(t), hints(h), last_graph(dicho_graph(NULL, 0)), gen(s) {}
  ~dichotomy_helper();
};

class dichotomy_node: public dependent_node {
  property res;
  dichotomy_graphs *graphs;
 public:
  dichotomy_node(property const &p, dichotomy_graphs *g)
    : dependent_node(UNION), res(p), graphs(g) { ++g->nb_ref; }
  ~dichotomy_node();
  virtual property const &get_result() const { return res; }
  using dependent_node::insert_pred;
  virtual void enlarge(property const &p) { if (!res.null()) res = boundify(p, res); }
  virtual property maximal_for(node const *) const;
};

property dichotomy_node::maximal_for(node const *n) const {
  if (n == get_subproofs()[0]) return n->get_result();
  return res;
}

dichotomy_graphs::~dichotomy_graphs()
{
  assert(nb_ref == 0);
  for(graph_vect::iterator i = graphs.begin(),
      i_end = graphs.end(); i != i_end; ++i)
  {
    delete *i;
  }
}

dichotomy_helper::~dichotomy_helper()
{
  delete last_graph.first;
  delete gen;
}

dichotomy_node::~dichotomy_node()
{
  clean_dependencies();
  if (--graphs->nb_ref == 0)
    delete graphs;
}

static bool find_negative(property &p, property_tree const &t)
{
  if (t.left)
    return find_negative(p, *t.left) || find_negative(p, *t.right);
  if (t.conjunction) return false;
  p = *t.atom;
  return true;
}

dicho_graph dichotomy_helper::try_hypothesis(dichotomy_failure *exn) const
{
  graph_t *g = new graph_t(top_graph, property_tree(tmp_hyp));
  g->populate(targets, hints, iter_max, NULL);
  if (g->get_contradiction() || targets.empty())
    return dicho_graph(g, iter_max);
  property_tree t;
  bool chg;
  if (targets.try_simplify(simpl_graph(g), chg, t) < 0)
    return dicho_graph(g, iter_max);
  if (exn)
  {
    if (find_negative(exn->expected, chg ? t : targets)) {
      if (node *n = g->find_already_known(exn->expected.real))
        exn->found = n->get_result();
    }
    exn->hyp = g->find_already_known(tmp_hyp.real)->get_result();
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
  if (proof_generator && (gen->merge() ||
        (g1.first->get_contradiction() && g2.first->get_contradiction())))
  {
    property p(*g1.first->get_hypotheses().atom);
    p.bnd() = interval(lower(p.bnd()), upper(g2.first->get_hypotheses().atom->bnd()));
    tmp_hyp = p;
    iter_max = g1.second + g2.second;
    dicho_graph g = try_hypothesis(NULL);
    if (g.first)
    {
      if (gen->merge() || g.first->get_contradiction())
      {
        // joined graph was successful, keep it as the last graph instead of g1 and g2
        delete g1.first;
        delete g2.first;
        last_graph = g;
        return;
      }
      delete g.first;
    }
  }
  // validate g1 and keep g2 as the last graph
  graphs->graphs.push_back(g1.first);
  last_graph = g2;
}

dichotomy_node *dichotomy_helper::generate_node(property const &p)
{
  property q;
  bool found_one = false;
  for (graph_vect::const_iterator i = graphs->graphs.begin(),
       i_end = graphs->graphs.end(); i != i_end; ++i)
  {
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
  dichotomy_node *n = new dichotomy_node(q, graphs);
  for (graph_vect::const_iterator i = graphs->graphs.begin(),
       i_end = graphs->graphs.end(); i != i_end; ++i)
  {
    graph_t *g = *i;
    if (node *m = g->get_contradiction()) n->insert_pred(m);
    else n->insert_pred(g->find_already_known(p.real));
  }
  return n;
}

void dichotomy_helper::dichotomize()
{
  number prev = number::neg_inf;
  number next = gen->next(iter_max);
  dichotomy_failure exn;
  if (next == number::pos_inf) throw exn;
  for (;;)
  {
    tmp_hyp.bnd() = interval(prev, next);
    //std::cerr << dump_property(tmp_hyp) << '\n';
    exn.hyp = tmp_hyp;
    dicho_graph g = try_hypothesis(&exn);
    if (!g.first) {
      if (is_singleton(exn.hyp.bnd())) throw exn;
      if (gen->split(next, iter_max)) continue;
      throw exn;
    }
    if (next < number::pos_inf) {
      try_graph(g);
      prev = next;
      next = gen->next(iter_max);
      continue;
    }
    if (graphs->graphs.empty()) {
      // if this is the second and last graph, do not try a merge
      if (last_graph.first) graphs->graphs.push_back(last_graph.first);
      last_graph = g;
    } else try_graph(g);
    graphs->graphs.push_back(last_graph.first);
    last_graph = dicho_graph(NULL, 0);
    return;
  }
}

/**
 * Applies a ::dichotomy_hint.
 */
void graph_t::dichotomize(dichotomy_hint const &hint, int iter_max)
{
  assert(top_graph == this);
  dichotomy_sequence hints;
  assert(hint.src.size() >= 1);
  dichotomy_var const &var = hint.src[0];
  if (hint.src.size() > 1) {
    dichotomy_hint h =
      { dvar_vect(hint.src.begin() + 1, hint.src.end()),
        hint.dst, hint.user_def };
    hints.push_back(h);
  }
  if (false) {
    no_range:
    if (warning_dichotomy_failure && hint.user_def)
      std::cerr << "Warning: case split on " << dump_real(var.real)
                << " has no range to split.\n";
    return;
  }
  interval bnd(number::neg_inf, number::pos_inf);
  if (node *varn = find_proof(predicated_real(var.real, PRED_BND)))
    bnd = varn->get_result().bnd();
  splitter *gen;
  property_tree targets;
  if (var.splitter & 1) {
    if (!is_bounded(bnd)) goto no_range;
    gen = new fixed_splitter(bnd, var.splitter / 2, iter_max);
  } else if (var.splitter) {
    gen = new point_splitter(bnd, (number_vect const *)var.splitter, iter_max);
  } else {
    targets = hint.dst;
    graph_t *g = this;
    while (g->father) g = g->father;
    targets.negate();
    targets.fill_undefined(g->hyps);
    if (targets.empty()) {
      if (warning_dichotomy_failure && hint.user_def)
        std::cerr << "Warning: case split on " << dump_real(var.real)
                  << " is not goal-driven anymore.\n";
      return;
    }
    if (targets.simplify(simpl_graph(this))) return;
    gen = new best_splitter(bnd, iter_max);
  }
  dichotomy_helper h(var.real, targets, hints, gen);
  try {
    h.dichotomize();
  } catch (dichotomy_failure const &e) {
    if (warning_dichotomy_failure && hint.user_def) {
      property const &h = e.hyp;
      if (h.real.null()) goto no_range;
      change_io_format dummy(IO_FULL);
      std::cerr << "Warning: when " << dump_real_short(h.real) << " is in "
                << h.bnd() << ", ";
      predicated_real const &dst = e.expected.real;
      if (dst.null())
        std::cerr << "nothing is satisfied.\n";
      else
      {
        std::cerr << dump_property(e.expected) << " cannot be proved";
        if (!e.found.real.null())
        {
          assert(e.expected.real == e.found.real);
          if (e.found.real.pred_bnd())
            std::cerr << " (best: " << e.found.bnd() << ')';
          else if (e.found.real.pred_cst())
            std::cerr << " (best: " << e.found.cst() << ')';
        }
        std::cerr << ".\n";
      }
    }
    delete h.graphs;
    return;
  }
  bool only_contradictions = true;
  typedef std::set< predicated_real > preal_set;
  preal_set reals;
  for (graph_vect::const_iterator i = h.graphs->graphs.begin(),
       i_end = h.graphs->graphs.end(); i != i_end; ++i)
  {
    graph_t *g = *i;
    if (g->contradiction) continue;
    only_contradictions = false;
    for (node_map::const_iterator j = g->known_reals.begin(),
         j_end = g->known_reals.end(); j != j_end; ++j)
      reals.insert(j->first);
    break;
  }
  assert(!contradiction);
  if (only_contradictions) {
    dichotomy_node *n = new dichotomy_node(property(), h.graphs);
    for (graph_vect::const_iterator i = h.graphs->graphs.begin(),
         i_end = h.graphs->graphs.end(); i != i_end; ++i)
    {
      n->insert_pred((*i)->get_contradiction());
    }
    set_contradiction(n);
    return;
  }
  ++h.graphs->nb_ref;
  for(preal_set::const_iterator i = reals.begin(), end = reals.end(); i != end; ++i) {
    property p(*i);
    if (node *n = find_already_known(*i)) p = n->get_result();
    if (node *n = h.generate_node(p)) try_node(n);
  }
  if (--h.graphs->nb_ref == 0) {
    delete h.graphs;
    if (warning_dichotomy_failure && hint.user_def)
      std::cerr << "Warning: case split on " << dump_real(var.real)
                << " has not produced any interesting new result.\n";
    return;
  }
  for (graph_vect::const_iterator i = h.graphs->graphs.begin(),
       i_end = h.graphs->graphs.end(); i != i_end; ++i)
  {
    (*i)->purge();
  }
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

void clear_splitter(unsigned long s)
{
  delete (number_vect *)s;
}
