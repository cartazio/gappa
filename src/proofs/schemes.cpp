#include <iostream>
#include <fstream>
#include <list>
#include <map>
#include <set>
#include <string>
#include <vector>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/schemes.hpp"

extern std::string parameter_schemes;

typedef std::set< ast_real const * > ast_real_set;
extern ast_real_set input_reals, output_reals;

struct scheme_factories: std::vector< scheme_factory const * > {
  ~scheme_factories() { for(iterator i = begin(), i_end = end(); i != i_end; ++i) delete *i; }
};
static scheme_factories factories;

scheme_factory::scheme_factory(predicated_real const &r): target(r) {
  factories.push_back(this);
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

typedef std::set< predicated_real > real_set;
static real_set missing_reals;

typedef std::vector< proof_scheme const * > scheme_vect;
static scheme_vect source_schemes;

/** Timestamp for the currently running graph algorithm. Increased each time an algorithm starts. */
static unsigned visit_counter = 0;

typedef std::set< proof_scheme const * > scheme_set;
struct real_dependency
{
  scheme_set dependent;
  scheme_set schemes;
  bool found;
  mutable unsigned visited;
  real_dependency(): found(false), visited(0) {}
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

/**
 * Marks the source schemes as visited and puts them into @a v.
 */
static void initialize_scheme_list(scheme_list &v)
{
  ++visit_counter;
  v.clear();
  for (scheme_vect::const_iterator i = source_schemes.begin(),
       i_end = source_schemes.end(); i != i_end; ++i)
  {
    proof_scheme const *s = *i;
    s->visited = visit_counter;
    v.push_back(s);
  }
}

/**
 * Marks as visited and inserts into @a v all the schemes that depend on @a real.
 */
static void insert_dependent(scheme_list &v, predicated_real const &real)
{
  scheme_set const &dep = reals[real].dependent;
  for (scheme_set::const_iterator i = dep.begin(),
       i_end = dep.end(); i != i_end; ++i)
  {
    proof_scheme const *s = *i;
    if (!s->can_visit()) continue;
    v.push_back(s);
  }
}

static void insert_dependent_init(scheme_list &v, predicated_real const &real) {
  scheme_set const &dep = reals[real].dependent;
  for(scheme_set::const_iterator i = dep.begin(), i_end = dep.end(); i != i_end; ++i) {
    proof_scheme const *s = *i;
    if (!s || s->visited == visit_counter) continue;
    preal_vect w = s->needed_reals();
    bool good = true;
    for(preal_vect::const_iterator j = w.begin(), j_end = w.end(); j != j_end; ++j)
      if (!reals[*j].found) { good = false; break; }
    if (!good) continue;
    bool &found = reals[s->real].found;
    // FIXME: ???
    if (w.size() > 0 && w[0] == s->real && !found) continue;
    s->visited = visit_counter;
    v.push_back(s);
    found = true;
  }
}

static void delete_scheme(proof_scheme const *s, predicated_real const *restricted_real) {
  // if there is a restriction, we are removing a scheme that depends on a real,
  // otherwise we are removing a scheme from a real; in both cases, we should
  // not modify the dependencies of this real
  preal_vect v = s->needed_reals();
  for(preal_vect::const_iterator i = v.begin(), end = v.end(); i != end; ++i) {
    predicated_real const &real = *i;
    if (restricted_real && real == *restricted_real) continue;
    missing_reals.insert(real);
    reals[real].dependent.erase(s);
  }
  if (restricted_real) reals[s->real].schemes.erase(s);
  delete s;
}

int stat_tested_real = 0, stat_discarded_real = 0;

static real_dependency &initialize_dependencies(predicated_real const &real) {
  real_dependencies::iterator it = reals.find(real);
  if (it != reals.end()) return it->second;
  // no dependencies yet, let's generate them
  ++stat_tested_real;
  it = reals.insert(std::make_pair(real, real_dependency())).first;
  real_dependency &dep = it->second;
  scheme_set &l = dep.schemes;
  for (scheme_factories::iterator i = factories.begin(),
       i_end = factories.end(); i != i_end; ++i) {
    scheme_factory const &f = **i;
    ast_real_vect holders;
    if (!f.target.null()) {
      if (f.target.pred() != real.pred()) continue;
      ast_real const *r1 = f.target.real(), *r2 = f.target.real2();
      if (!match(real.real(), r1, holders) ||
          (r2 && !match(real.real2(), r2, holders)))
        continue;
      if (holders.size() >= 2 && (!holders[0] || !holders[1])) {
        assert(holders[0] || holders[1]);
        int p = !holders[1];
        link_map const *lm = p ? &approximates : &accurates;
        link_map::const_iterator k = lm->find(holders[1 - p]);
        if (k == lm->end()) continue;
        ast_real_set const &s = k->second;
        for (ast_real_set::const_iterator j = s.begin(), j_end = s.end(); j != j_end; ++j) {
          holders[p] = *j;
          if (proof_scheme *s = f(real, holders)) l.insert(s);
        }
        continue;
      }
    }
    if (proof_scheme *s = f(real, holders)) l.insert(s);
  }
  // create the dependencies
  for (scheme_set::const_iterator i = l.begin(), i_end = l.end(); i != i_end; ++i) {
    proof_scheme const *s = *i;
    preal_vect v = s->needed_reals();
    for(preal_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
      initialize_dependencies(*j).dependent.insert(s);
    missing_reals.insert(s->real);
  }
  return it->second;
}

typedef std::list< predicated_real > real_list;

/**
 * Tells if the scheme @a s depends indirectly on @a real only.
 *
 * @note Scans only 10 reals below @a real before it assumes there are
 *       other dependencies.
 */
bool depends_only_on(proof_scheme const *s, predicated_real const &real)
{
  preal_vect v = s->needed_reals();
  if (v.empty()) return false;
  ++visit_counter;
  reals[real].visited = visit_counter;
  real_list pending_reals;
  for (preal_vect::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
    if (reals[*i].can_visit()) pending_reals.push_back(*i);
  int iter = 0;
  while (!pending_reals.empty())
  {
    if (iter++ == 10) return false;
    predicated_real r = pending_reals.front();
    pending_reals.pop_front();
    scheme_set const &v = reals[r].schemes;
    for (scheme_set::const_iterator i = v.begin(), i_end = v.end(); i != i_end; ++i)
    {
      proof_scheme const *t = *i;
      if (!t) return false;
      preal_vect w = t->needed_reals();
      if (w.empty()) return false;
      for (preal_vect::const_iterator j = w.begin(), j_end = w.end(); j != j_end; ++j)
        if (reals[*j].can_visit()) pending_reals.push_back(*j);
    }
  }
  return true;
}

ast_real_vect generate_proof_paths() {
  for(ast_real_set::const_iterator i = output_reals.begin(), i_end = output_reals.end(); i != i_end; ++i)
    initialize_dependencies(predicated_real(*i, PRED_BND)).dependent.insert(NULL);
  // initialize hypothesis reals to handle contradictions
  for(ast_real_set::const_iterator i = input_reals.begin(), i_end = input_reals.end(); i != i_end; ++i) {
    real_dependency &r = initialize_dependencies(predicated_real(*i, PRED_BND));
    r.schemes.insert(NULL);
    r.dependent.insert(NULL);
    r.found = true;
  }
  // setup the source schemes
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    real_dependency &r = i->second;
    for(scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j) {
      proof_scheme const *s = *j;
      if (s && s->needed_reals().empty()) {
        source_schemes.push_back(s);
        r.found = true;
      }
    }
  }
  // find reachable schemes starting from sources and inputs
  scheme_list missing_schemes;
  initialize_scheme_list(missing_schemes);
  for(ast_real_set::const_iterator i = input_reals.begin(),
      i_end = input_reals.end(); i != i_end; ++i)
    insert_dependent_init(missing_schemes, predicated_real(*i, PRED_BND));
  while (!missing_schemes.empty()) {
    proof_scheme const *s = missing_schemes.front();
    missing_schemes.pop_front();
    insert_dependent_init(missing_schemes, s->real);
  }
  // remove unreachable schemes
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    real_dependency &r = i->second;
    scheme_set v;
    v.swap(r.schemes);
    for(scheme_set::iterator j = v.begin(), j_end = v.end(); j != j_end; ++j) {
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
      if (!s || !depends_only_on(s, real)) r.schemes.insert(s);
      else delete_scheme(s, NULL);
    }
  }
  // find reals reaching to outputs
  real_list pending_reals;
  ++visit_counter;
  for (ast_real_set::const_iterator i = output_reals.begin(),
       i_end = output_reals.end(); i != i_end; ++i)
  {
    predicated_real r(*i, PRED_BND);
    if (reals[r].can_visit()) pending_reals.push_back(r);
  }
  for (ast_real_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    predicated_real r(*i, PRED_BND);
    if (reals[r].can_visit()) pending_reals.push_back(r);
  }
  while (!pending_reals.empty())
  {
    predicated_real r = pending_reals.front();
    pending_reals.pop_front();
    scheme_set const &v = reals[r].schemes;
    for (scheme_set::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j)
    {
      proof_scheme const *s = *j;
      if (!s) continue;
      preal_vect w = s->needed_reals();
      for (preal_vect::const_iterator k = w.begin(), k_end = w.end(); k != k_end; ++k)
        if (reals[*k].can_visit()) pending_reals.push_back(*k);
    }
  }
  // remove schemes from unreachable reals
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
  {
    real_dependency &r = i->second;
    if (r.visited == visit_counter) continue;
    for(scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
      if (*j) delete_scheme(*j, NULL);
    r.schemes.clear();
  }
  // remove useless reals
  while (!missing_reals.empty()) {
    predicated_real const &real = *missing_reals.begin();
    real_dependency &r = reals[real];
    if (r.schemes.empty() || r.dependent.empty()) {
      for(scheme_set::const_iterator i = r.dependent.begin(), i_end = r.dependent.end(); i != i_end; ++i) {
        // if we are here, the real has no more scheme, so erase all the schemes that were relying on it
        proof_scheme const *p = *i;
        if (p) // just in case it is a goal real
          delete_scheme(p, &real);
      }
      for(scheme_set::const_iterator i = r.schemes.begin(), i_end = r.schemes.end(); i != i_end; ++i) {
        // if we are here, no scheme needs this real anymore, so erase all the schemes of the real
        proof_scheme const *p = *i;
        if (p) // just in case it is a hypothesis real
          delete_scheme(p, NULL);
      }
      reals.erase(real);
      ++stat_discarded_real;
    }
    missing_reals.erase(real);
  }
  // correctly setup the source schemes now, and clean the dependencies
  source_schemes.clear();
  for(real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i) {
    real_dependency &r = i->second;
    r.schemes.erase(NULL);
    for(scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j) {
      proof_scheme const *s = *j;
      if (s->needed_reals().empty())
        source_schemes.push_back(s);
    }
    r.dependent.erase(NULL);
  }
  // generate the scheme graph
  if (!parameter_schemes.empty())
  {
    std::ofstream out(parameter_schemes.c_str());
    int num_th = 0;
    out << "digraph {\n";
    for (real_dependencies::iterator i = reals.begin(), i_end = reals.end(); i != i_end; ++i)
    {
      real_dependency &r = i->second;
      for (scheme_set::iterator j = r.schemes.begin(), j_end = r.schemes.end(); j != j_end; ++j)
      {
        ++num_th;
        out << "  \"" << dump_real(i->first) << "\" -> \"T" << num_th << "\";\n"
             << "  \"T" << num_th << "\" [shape=box];\n";
        preal_vect v = (*j)->needed_reals();
        for (preal_vect::const_iterator k = v.begin(), k_end = v.end(); k != k_end; ++k)
          out << "  \"T" << num_th << "\" -> \"" << dump_real(*k) << "\";\n";
      }
    }
    out << "}\n";
    out.close();
  }
  // find unreachable outputs
  ast_real_vect missing_targets;
  for(ast_real_set::iterator i = output_reals.begin(), end = output_reals.end(); i != end; ++i) {
    real_dependencies::iterator j = reals.find(predicated_real(*i, PRED_BND));
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

node *find_proof(property const &res) {
  node *n = find_proof(res.real);
  return (n && n->get_result().implies(res)) ? n : NULL;
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

/**
 * Fills this graph by iteratively applying theorems until
 * \li @a goals is statisfied, or
 * \li a contradiction is found, or
 * \li a fixpoint is reached for the results, or
 * \li an upper bound on the number of iterations is reached.
 *
 * @return true if a contradiction is found.
 */
bool graph_t::populate(property_tree const &goals, dichotomy_sequence const &dichotomy, int iter_max)
{
  if (contradiction)
    return true;
  iter_max = iter_max / (2 * dichotomy.size() + 1);
  property_tree current_goals = goals;
  graph_loader loader(this);
  for (dichotomy_sequence::const_iterator dichotomy_it = dichotomy.begin(),
       dichotomy_end = dichotomy.end(); /*nothing*/; ++dichotomy_it)
  {
    scheme_list missing_schemes;
    initialize_scheme_list(missing_schemes);
    for (node_map::const_iterator i = known_reals.begin(),
         i_end = known_reals.end(); i != i_end; ++i)
      insert_dependent(missing_schemes, i->first);
    int iter = -(int)missing_schemes.size();
    while (iter++ != iter_max && !missing_schemes.empty())
    {
      proof_scheme const *s = missing_schemes.front();
      missing_schemes.pop_front();
      s->visited = 0; // allows the scheme to be reused later, if needed
      ++stat_tested_th;
      node *n = s->generate_proof();
      if (!n || !try_real(n)) continue;		// the scheme did not find anything useful
      if (contradiction) return true;		// we have got a contradiction, everything is true
      insert_dependent(missing_schemes, s->real);
      if (current_goals.empty()) continue;	// originally empty, we are striving for a contradiction
      if (s->real.pred() != PRED_BND) continue;
      current_goals.remove(n->get_result());
      if (current_goals.empty()) return false;	// now empty, there is nothing left to prove
    }
    if (iter > iter_max)
      std::cerr << "Warning: maximum number of iterations reached.\n";
    if (dichotomy_it == dichotomy_end) return false;
    if (dichotomize(current_goals, *dichotomy_it, iter_max) && contradiction)
      return true;
  }
}
