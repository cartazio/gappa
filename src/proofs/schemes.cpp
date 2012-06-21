/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <iostream>
#include <fstream>
#include <list>
#include <map>
#include <typeinfo>
#include <set>
#include <string>
#include <vector>
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

extern std::string parameter_schemes;
extern backend *proof_generator;

bool is_unknown_theorem(char const *th)
{
  return proof_generator && !proof_generator->is_known(th);
}

typedef std::set< predicated_real > preal_set;
extern preal_set input_reals, output_reals;

struct scheme_factories: std::vector< scheme_factory const * > {
  ~scheme_factories() { for(iterator i = begin(), i_end = end(); i != i_end; ++i) delete *i; }
};
static scheme_factories *factories;

scheme_factory::scheme_factory(predicated_real const &r): target(r) {
  if (!factories) factories = new scheme_factories;
  factories->push_back(this);
}

struct factorx_wrapper: scheme_factory {
  typedef factory_creator::factorx_fun factory_fun;
  factory_fun fun;
  factorx_wrapper(factory_fun f, predicated_real const &r)
  : scheme_factory(r), fun(f) {}
  virtual proof_scheme *operator()(predicated_real const &r, ast_real_vect const &h) const
  { return (*fun)(r, h); }
};

struct factory_wrapper: scheme_factory {
  typedef factory_creator::factory_fun factory_fun;
  factory_fun fun;
  factory_wrapper(factory_fun f)
  : scheme_factory(predicated_real()), fun(f) {}
  virtual proof_scheme *operator()(predicated_real const &r, ast_real_vect const &) const
  { return r.pred() == PRED_BND ? (*fun)(r.real()) : NULL; }
};

struct factorz_wrapper: scheme_factory {
  typedef factory_creator::factorz_fun factory_fun;
  factory_fun fun;
  factorz_wrapper(factory_fun f)
  : scheme_factory(predicated_real()), fun(f) {}
  virtual proof_scheme *operator()(predicated_real const &r, ast_real_vect const &) const
  { return (*fun)(r); }
};

factory_creator::factory_creator(factorx_fun f, predicated_real const &r)
{ new factorx_wrapper(f, r); }

factory_creator::factory_creator(factory_fun f)
{ new factory_wrapper(f); }

factory_creator::factory_creator(factorz_fun f)
{ new factorz_wrapper(f); }

typedef std::vector< proof_scheme const * > scheme_vect;
static scheme_vect source_schemes;

/** Timestamp for the currently running graph algorithm. Increased each time an algorithm starts. */
static unsigned visit_counter = 0;

typedef std::set< proof_scheme const * > scheme_set;
struct real_dependency
{
  scheme_set dependent;
  scheme_set schemes;
  mutable unsigned visited;
  real_dependency(): visited(0) {}
  bool can_visit() const;
};
typedef std::map< predicated_real, real_dependency > real_dependencies;
static real_dependencies reals;

typedef std::list< proof_scheme const * > scheme_list;

/**
 * Tells if the scheme has yet to be visited by the current graph algorithm.
 * In that case, the function updates the #visited timestamp so that the next call returns false.
 */
bool proof_scheme::can_visit() const
{
  if (visited == visit_counter) return false;
  visited = visit_counter;
  return true;
}

/**
 * Tells if the real has yet to be visited by the current graph algorithm.
 * In that case, the function updates the #visited timestamp so that the next call returns false.
 */
bool real_dependency::can_visit() const
{
  if (visited == visit_counter) return false;
  visited = visit_counter;
  return true;
}

/** Priority queue for storing schemes. */
struct scheme_queue
{
  static int const
    nb_queues = 10,		/**< Number of queues. */
    score_per_queue = 3,	/**< Granularity of the score. */
    pop_per_queue = 3,		/**< Period for removing from a lower queue. */
    success_score = 6;		/**< Score increase for successful schemes. */
  scheme_queue();
  /** Decreases the score of @a s and stores it in the corresponding queue. */
  void push(proof_scheme const *a);
  /**
   * Removes a scheme from a queue and returns it.
   * Queues with the highest scores are emptied more often.
   */
  proof_scheme const *pop();
  scheme_list queues[nb_queues];
  int counters[nb_queues];
};

scheme_queue::scheme_queue()
{
  for (int i = 0; i < nb_queues; ++i) counters[i] = 0;
}

void scheme_queue::push(proof_scheme const *s)
{
  int zero_queue = nb_queues / 2,
      min_score = - zero_queue * score_per_queue,
      max_score = (nb_queues - zero_queue - 1) * score_per_queue;
  --s->score;
  if (s->score <= min_score) s->score = min_score; else
  if (s->score >= max_score) s->score = max_score;
  int num = (s->score - min_score) / score_per_queue;
  queues[num].push_back(s);
}

proof_scheme const *scheme_queue::pop()
{
  for (int j = 0; j < 2; ++j)
  {
    // Two runs, to ensure we return a scheme if there is one.
    for (int i = nb_queues - 1; i >= 0; --i)
    {
      if (queues[i].empty()) continue;
      if (++counters[i] == pop_per_queue)
      {
        counters[i] = 0;
        continue;
      }
      proof_scheme const *s = queues[i].front();
      queues[i].pop_front();
      return s;
    }
  }
  return NULL;
}

/**
 * Marks the source schemes as visited and puts them into @a v.
 */
static void initialize_scheme_list(scheme_queue &v)
{
  ++visit_counter;
  for (scheme_vect::const_iterator i = source_schemes.begin(),
       i_end = source_schemes.end(); i != i_end; ++i)
  {
    proof_scheme const *s = *i;
    s->visited = visit_counter;
    v.push(s);
  }
}

/**
 * Marks as visited and inserts into @a v all the schemes (except @a ss) that depend on @a real.
 */
static void insert_dependent(scheme_queue &v, predicated_real const &real, proof_scheme const *ss = NULL)
{
  scheme_set const &dep = reals[real].dependent;
  for (scheme_set::const_iterator i = dep.begin(),
       i_end = dep.end(); i != i_end; ++i)
  {
    proof_scheme const *s = *i;
    if (s == ss || !s->can_visit()) continue;
    v.push(s);
  }
}

static void delete_scheme(proof_scheme const *s, predicated_real const *restricted_real) {
  // if there is a restriction, we are removing a scheme that depends on a real,
  // otherwise we are removing a scheme from a real; in both cases, we should
  // not modify the dependencies of this real
  preal_vect v = s->needed_reals;
  for(preal_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    predicated_real const &real = *i;
    if (restricted_real && real == *restricted_real) continue;
    reals[real].dependent.erase(s);
  }
  if (restricted_real) reals[s->real].schemes.erase(s);
  delete s;
}

int stat_tested_real = 0, stat_discarded_real = 0;

static real_dependency &initialize_dependencies(predicated_real const &real)
{
  real_dependencies::iterator it = reals.find(real);
  if (it != reals.end()) return it->second;
  // no dependencies yet, let's generate them
  ++stat_tested_real;
  it = reals.insert(std::make_pair(real, real_dependency())).first;
  real_dependency &dep = it->second;
  scheme_set &l = dep.schemes;
  for (scheme_factories::iterator i = factories->begin(),
       i_end = factories->end(); i != i_end; ++i)
  {
    scheme_factory const &f = **i;
    ast_real_vect holders;
    if (f.target.null())
    {
      // no embedded pattern (or no hole left in the pattern, see below)
      no_hole:
      if (proof_scheme *s = f(real, holders)) l.insert(s);
      continue;
    }
    // there is an embedded pattern, match it against the current real
    if (f.target.pred() != real.pred()) continue;
    ast_real const *r1 = f.target.real(), *r2 = f.target.real2();
    if (!match(real.real(), r1, holders) ||
        (r2 && !match(real.real2(), r2, holders)))
      continue;
    // the embedded pattern is a match, try generating schemes
    if (holders.size() < 2 || (holders[0] && holders[1]))
      goto no_hole;
    assert(holders[0] || holders[1]);
    int p = !holders[1];
    // pattern position p is not filled, use approx/accurate pairs
    link_map const *lm = p ? &approximates : &accurates;
    link_map::const_iterator k = lm->find(holders[1 - p]);
    if (k == lm->end()) continue;
    ast_real_set const &s = k->second;
    for (ast_real_set::const_iterator j = s.begin(), j_end = s.end(); j != j_end; ++j) {
      holders[p] = *j;
      if (proof_scheme *s = f(real, holders)) l.insert(s);
    }
  }
  // create the dependencies
  for (scheme_set::const_iterator i = l.begin(), i_end = l.end(); i != i_end; ++i)
  {
    proof_scheme const *s = *i;
    preal_vect v = s->needed_reals;
    for(preal_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
      initialize_dependencies(*j).dependent.insert(s);
  }
  return it->second;
}

typedef std::list< predicated_real > preal_list;

/**
 * Tells if the scheme @a s depends indirectly on @a real only.
 *
 * @note Scans only 10 reals below @a real before it assumes there are
 *       other dependencies.
 */
static bool depends_only_on(proof_scheme const *s, predicated_real const &real)
{
  preal_vect v = s->needed_reals;
  if (v.empty()) return false;
  ++visit_counter;
  reals[real].visited = visit_counter;
  preal_list pending_reals;
  for (preal_vect::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
    if (reals[*i].can_visit()) pending_reals.push_back(*i);
  int iter = 0;
  while (!pending_reals.empty())
  {
    if (iter++ == 10) return false;
    predicated_real r = pending_reals.back();
    pending_reals.pop_back();
    scheme_set const &v = reals[r].schemes;
    for (scheme_set::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
    {
      proof_scheme const *t = *i;
      if (!t) return false;
      preal_vect w = t->needed_reals;
      if (w.empty()) return false;
      for (preal_vect::const_iterator j = w.begin(), j_end = w.end(); j != j_end; ++j)
        if (reals[*j].can_visit()) pending_reals.push_back(*j);
    }
  }
  return true;
}

/**
 * Marks all the schemes and reals reachable from @a real.
 */
static void mark_dependent_schemes(predicated_real const &real)
{
  preal_list pending_reals;
  if (!reals[real].can_visit()) return;
  pending_reals.push_back(real);
  while (!pending_reals.empty())
  {
    predicated_real r = pending_reals.back();
    pending_reals.pop_back();
    scheme_set const &v = reals[r].dependent;
    for (scheme_set::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
    {
      proof_scheme const *s = *i;
      if (!s || !s->can_visit()) continue;
      if (reals[s->real].can_visit()) pending_reals.push_back(s->real);
    }
  }
}

/**
 * Marks all the reals potentially useful for reaching @a real.
 */
static void mark_useful_reals(predicated_real const &real)
{
  preal_list pending_reals;
  if (!reals[real].can_visit()) return;
  pending_reals.push_back(real);
  while (!pending_reals.empty())
  {
    predicated_real r = pending_reals.back();
    pending_reals.pop_back();
    scheme_set const &v = reals[r].schemes;
    for (scheme_set::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
    {
      proof_scheme const *s = *i;
      if (!s) continue;
      preal_vect w = s->needed_reals;
      for (preal_vect::const_iterator j = w.begin(), j_end = w.end(); j != j_end; ++j)
        if (reals[*j].can_visit()) pending_reals.push_back(*j);
    }
  }
}

/**
 * Detects some schemes known to be useless.
 */
static bool is_useless_scheme(proof_scheme const *s)
{
  predicated_real rfix = s->real;
  if (rfix.pred() != PRED_FIX) return false;
  preal_vect v = s->needed_reals;
  if (v.size() != 2) return false;
  predicated_real rflt = v[0], rabs = v[1];
  if (rflt != predicated_real(rfix.real(), PRED_FLT)) return false;
  if (rabs != predicated_real(rfix.real(), PRED_ABS)) return false;
  real_dependency const &r = reals[rflt];
  if (r.schemes.size() != 2) return false;
  v = (*r.schemes.begin())->needed_reals;
  preal_vect v2 = (*++r.schemes.begin())->needed_reals;
  if (v.size() < v2.size()) std::swap(v, v2);
  if (v.size() != 2 || v2.size() != 1) return false;
  if (v[0] != rfix || v[1] != rabs || v2[0] != rabs) return false;
  return true;
}

/**
 * Generates all the schemes needed for linking inputs and outputs.
 */
preal_vect generate_proof_paths()
{
  // recursively search schemes needed for output reals
  for (preal_set::const_iterator i = output_reals.begin(),
       i_end = output_reals.end(); i != i_end; ++i)
  {
    real_dependency &r = initialize_dependencies(*i);
    r.dependent.insert(NULL);
  }
  // initialize hypothesis reals to handle contradictions
  for (preal_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    real_dependency &r = initialize_dependencies(*i);
    r.schemes.insert(NULL);
    r.dependent.insert(NULL);
  }
  // find reachable schemes starting from source schemes and inputs, then remove unreachable schemes
  ++visit_counter;
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
    {
      proof_scheme const *s = *j;
      if (!s || !s->needed_reals.empty()) continue;
      s->visited = visit_counter;
      mark_dependent_schemes(s->real);
    }
  }
  for (preal_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    mark_dependent_schemes(*i);
  }
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    scheme_set v;
    v.swap(r.schemes);
    for (scheme_set::iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
    {
      proof_scheme const *s = *j;
      if (!s || s->visited == visit_counter) r.schemes.insert(s);
      else delete_scheme(s, NULL);
    }
  }
  // remove useless schemes
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    predicated_real const &real = i->first;
    real_dependency &r = i->second;
    scheme_set v;
    v.swap(r.schemes);
    for (scheme_set::iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
    {
      proof_scheme const *s = *j;
      if (!s || !(depends_only_on(s, real) || is_useless_scheme(s)))
        r.schemes.insert(s);
      else delete_scheme(s, NULL);
    }
  }
  // find reals reaching to outputs, then remove unneeded reals
  ++visit_counter;
  for (preal_set::const_iterator i = output_reals.begin(),
       i_end = output_reals.end(); i != i_end; ++i)
  {
    mark_useful_reals(*i);
  }
  for (preal_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    mark_useful_reals(*i);
  }
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    if (r.visited == visit_counter) continue;
    for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
      if (*j) delete_scheme(*j, NULL);
    r.schemes.clear();
  }
  // remove reals without any scheme
  ++visit_counter;
  preal_list pending_reals;
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    if (!i->second.schemes.empty()) continue;
    pending_reals.push_back(i->first);
    i->second.visited = visit_counter;
  }
  while (!pending_reals.empty())
  {
    predicated_real real = pending_reals.back();
    pending_reals.pop_back();
    real_dependency &r = reals[real];
    for (scheme_set::const_iterator i = r.dependent.begin(),
         i_end = r.dependent.end(); i != i_end; ++i)
    {
      proof_scheme const *s = *i;
      if (!s) continue;
      predicated_real u = s->real;
      real_dependency const &t = reals[u];
      delete_scheme(s, &real);
      if (t.schemes.empty() && t.can_visit()) pending_reals.push_back(u);
    }
    reals.erase(real);
    ++stat_discarded_real;
  }
  // setup the source schemes now, and clean the dependencies
  for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    r.schemes.erase(NULL);
    for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
    {
      proof_scheme const *s = *j;
      if (s->needed_reals.empty())
        source_schemes.push_back(s);
    }
    r.dependent.erase(NULL);
  }
  // generate the scheme graph
  if (!parameter_schemes.empty())
  {
    std::ofstream out(parameter_schemes.c_str());
    out << "digraph {\n  node [shape=record];\n";
    for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
    {
      real_dependency &r = i->second;
      std::string var = dump_real(i->first);
      out << "  \"" << var << "\" [label=\"{";
      for (std::string::const_iterator j = var.begin(), j_end = var.end(); j != j_end; ++j)
      {
        switch (*j) {
          case '<': out << "&lt;"; break;
          case '>': out << "&gt;"; break;
          case '|': out << "&#124;"; break;
          default: out << *j;
        }
      }
      int num_th = 0;
      for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
        out << "|<" << ++num_th << '>' << typeid(**j).name();
      out << "}\"];\n";
      num_th = 0;
      for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
      {
        ++num_th;
        preal_vect v = (*j)->needed_reals;
        for (preal_vect::const_iterator k = v.begin(), k_end = v.end(); k != k_end; ++k)
          out << "  \"" << var << "\":" << num_th << " -> \"" << dump_real(*k) << "\";\n";
      }
    }
    out << "}\n";
    out.close();
  }
  // find unreachable outputs
  preal_vect missing_targets;
  for (preal_set::iterator i = output_reals.begin(),
       i_end = output_reals.end(); i != i_end; ++i)
  {
    real_dependencies::iterator j = reals.find(*i);
    if (j == reals.end())
      missing_targets.push_back(*i);
  }
  return missing_targets;
}

#ifdef LEAK_CHECKER
struct proof_paths_cleaner {
  ~proof_paths_cleaner();
};

proof_paths_cleaner::~proof_paths_cleaner() {
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    scheme_set &s = i->second.schemes;
    for(scheme_set::iterator j = s.begin(), j_end = s.end(); j != j_end; ++j)
      delete *j;
  }
}

static proof_paths_cleaner dummy;
#endif // LEAK_CHECKER

node *find_proof(property const &res, bool implies)
{
  node *n = find_proof(res.real);
  if (!n) return NULL;
  if (implies && !n->get_result().implies(res)) return NULL;
  if (!implies) {
    if (!res.real.pred_bnd()) return NULL;
    property p = n->get_result();
    p.intersect(res);
    if (!is_empty(p.bnd())) return NULL;
  }
  return n;
}

bool fill_hypotheses(property *hyp, preal_vect const &v) {
  for(preal_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    node *n = find_proof(*i);
    if (!n) return false;
    *(hyp++) = n->get_result();
  }
  return true;
}

int stat_tested_th = 0;

extern bool goal_reduction;

static bool reduce_goal(property_tree &current_goals,
  property_tree &current_targets, scheme_queue *missing_schemes)
{
  if (!goal_reduction || current_goals.empty() ||
      (current_goals->conjunction &&
       current_goals->leaves.size() + current_goals->subtrees.size() > 1))
    return false;

  std::vector<property_tree::leave> old_leaves = current_goals->leaves;
  for (std::vector<property_tree::leave>::const_iterator i = old_leaves.begin(),
       i_end = old_leaves.end(); i != i_end; ++i)
  {
    if (!i->first.real.pred_bnd() || !is_defined(i->first.bnd())) continue;
    node *m;
    if (!i->second) {
      m = create_theorem(0, NULL, i->first, "$LOGIC");
    } else {
      m = find_proof(i->first.real);
      if (!m) continue;
      property const &p = m->get_result();
      interval const &h = p.bnd(), &g = i->first.bnd();
      if (is_singleton(g)) continue;
      if (lower(h) >= lower(g)) {
        m = create_theorem(0, NULL, property(p.real,
          interval(upper(g), upper(h))), "$LOGIC");
      } else if (upper(h) <= upper(g)) {
        m = create_theorem(0, NULL, property(p.real,
          interval(lower(h), lower(g))), "$LOGIC");
      } else continue;
    }
    if (!top_graph->try_real(m)) continue;
    if (top_graph->get_contradiction()) return true;
    if (missing_schemes) insert_dependent(*missing_schemes, i->first.real);
    if (current_goals.empty()) continue;
    if (current_goals.simplify(m->get_result()) > 0) {
      top_graph->set_contradiction(m);
      return true;
    }
    if (!current_targets.empty() && current_targets.simplify(m->get_result()))
      return true;
  }
  return false;
}

/**
 * Fills this graph by iteratively applying theorems until
 * \li @a targets are satisfied, or
 * \li a contradiction (possibly with @a goals) is found, or
 * \li a fixpoint is reached for the results, or
 * \li an upper bound on the number of iterations is reached.
 */
void graph_t::populate(property_tree const &goals, property_tree const &targets,
  dichotomy_sequence const &dichotomy, int iter_max)
{
  if (contradiction) return;
  iter_max = iter_max / (2 * dichotomy.size() + 1);
  property_tree current_goals = goals, current_targets = targets;
  graph_loader loader(this);

  if (reduce_goal(current_goals, current_targets, NULL))
    return;

  for (dichotomy_sequence::const_iterator dichotomy_it = dichotomy.begin(),
       dichotomy_end = dichotomy.end(); /*nothing*/; ++dichotomy_it)
  {
    scheme_queue missing_schemes;
    initialize_scheme_list(missing_schemes);
    int iter = 0;
    for (node_map::const_iterator i = known_reals.begin(),
         i_end = known_reals.end(); i != i_end; ++i)
    {
      insert_dependent(missing_schemes, i->first);
      --iter;
    }
    proof_scheme const *s;
    while (iter++ != iter_max && ((s = missing_schemes.pop())))
    {
      s->visited = 0; // allows the scheme to be reused later, if needed
      ++stat_tested_th;
      property hyps[s->needed_reals.size()];
      if (!fill_hypotheses(hyps, s->needed_reals)) {
        // The scheme is missing some hypotheses.
        continue;
      }
      node *n = s->generate_proof(hyps);
      if (!n || !try_real(n)) {
        // The scheme failed or did not find anything new.
        continue;
      }
      s->score += scheme_queue::success_score;
      if (contradiction) {
        // We have got a contradiction, everything is true.
        return;
      }
      //std::cout << dump_property(n->get_result()) << '\t' << typeid(*s).name() << '\n';
      insert_dependent(missing_schemes, s->real, s);
      if (current_goals.empty()) {
        // Originally empty, we are striving for a contradiction.
        continue;
      }
      if (s->real.pred() != PRED_BND && s->real.pred() != PRED_REL) continue;
      if (current_goals.simplify(n->get_result()) > 0) {
        // Now empty, there is nothing left to prove.
        if (goal_reduction) set_contradiction(n);
        return;
      }
      if (!current_targets.empty() && current_targets.simplify(n->get_result())) return;
      if (reduce_goal(current_goals, current_targets, &missing_schemes)) return;
    }
    if (iter > iter_max)
      std::cerr << "Warning: maximum number of iterations reached.\n";
    if (dichotomy_it == dichotomy_end)
    {
      if (!goal_reduction || current_goals.empty()) return;
      static ast_real_set already;
      splitting s;
      current_goals.get_splitting(s);
      unsigned max_pts = 0;
      splitting::value_type const *sv = NULL;
      for (splitting::const_iterator i = s.begin(), i_end = s.end(); i != i_end; ++i)
      {
        if (i->first.real2() || i->second.size() <= max_pts ||
            already.find(i->first.real()) != already.end())
          continue;
        node *n = find_proof(i->first.real());
        if (!n || is_singleton(n->get_result().bnd())) continue;
        max_pts = i->second.size();
        sv = &*i;
      }
      if (max_pts <= 1) return;
      ast_real_set save = already;
      unsigned long ds = 0;
      number prev = number::neg_inf;
      for (split_point_mset::const_iterator i = sv->second.begin(),
           i_end = sv->second.end(); i != i_end; ++i)
      {
        if (i->pt == prev) continue;
        ds = fill_splitter(ds, *i);
        prev = i->pt;
      }
      already.insert(sv->first.real());
      dichotomy_var dv = { sv->first.real(), ds };
      dichotomy_hint dh = { dvar_vect(1, dv), property_tree() };
      dichotomize(current_goals, dh, iter_max);
      already = save;
      return;
    }
    dichotomize(current_goals, *dichotomy_it, iter_max);
    if (contradiction) return;
  }
}
