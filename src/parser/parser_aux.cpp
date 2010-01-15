#include <algorithm>
#include <cassert>
#include <iostream>
#include <sstream>
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"
#include "proofs/rewriting.hpp"

typedef std::set< ast_real const * > real_set;
real_set free_variables;
typedef std::set< predicated_real > preal_set;
preal_set input_reals, output_reals;

interval create_interval(ast_number const *, ast_number const *, bool);
void find_unknown_reals(real_set &, ast_real const *);

extern bool warning_unbound_variable;

static property generate_property(ast_atom_bound const &p, bool goal)
{
  predicated_real pr;
  if (p.real2)
    pr = predicated_real(p.real, p.real2, PRED_REL);
  else
    pr = predicated_real(p.real, PRED_BND);
  output_reals.insert(pr);
  property r(pr);
  if (p.lower || p.upper)
  {
    interval &bnd = r.bnd();
    bnd = create_interval(p.lower, p.upper, !goal);
    if (is_empty(bnd))
    {
      std::cerr << "Error: the range of " << dump_real_short(pr)
                << " is an empty interval.\n";
      exit(1);
    }
    if (pr.real2() && lower(bnd) <= number(-1))
    {
      std::cerr << "Error: the range of " << dump_real_short(pr)
                << " contains values smaller or equal to -1.\n";
      exit(1);
    }
  }
  else if (!goal)
  {
    std::cerr << "Error: undefined intervals are restricted to conclusions.\n";
    exit(1);
  }
  return r;
}

static void generate_tree(property_tree &tree, ast_prop const *p, bool positive)
{
  switch (p->type) {
  case PROP_ATOM:
    tree->leaves.push_back(property_tree::leave
      (generate_property(*p->atom, positive), positive));
    break;
  case PROP_IMPL:
  case PROP_AND:
  case PROP_OR: {
    property_tree *dst = &tree;
    bool conjunction = (p->type == PROP_AND) ^ !positive;
    if (tree->conjunction != conjunction) {
      tree->subtrees.push_back(new property_tree::data(conjunction));
      dst = &tree->subtrees.back();
    }
    generate_tree(*dst, p->lhs, positive ^ (p->type == PROP_IMPL));
    generate_tree(*dst, p->rhs, positive);
    break; }
  case PROP_NOT:
    generate_tree(tree, p->lhs, !positive);
    break;
  }
}

static void register_approx(ast_real const *r1, ast_real const *r2)
{
  accurates[r1].insert(r2);
  approximates[r2].insert(r1);
}

void check_approx(ast_real const *real)
{
  real_op const *o = boost::get< real_op const >(real);
  if (!o) return;
  // look for an approx/accurate pair
  if (o->type == UOP_ABS)
    o = boost::get< real_op const >(o->ops[0]);
  ast_real const *r = NULL;
  if (o && o->type == BOP_DIV)
  {
    r = o->ops[1];
    o = boost::get< real_op const >(o->ops[0]);
  }
  if (o && o->type == BOP_SUB && (!r || r == o->ops[1]))
    register_approx(o->ops[0], o->ops[1]);
}

static void parse_property_tree(ast_prop const *p, context &ctx)
{
  property_tree tree(new property_tree::data(false));
  generate_tree(tree, p, true);

  std::vector<property_tree::leave> new_leaves;

  // for any goal x>=b or x<=b, add the converse inequality as a hypothesis
  for (std::vector<property_tree::leave>::const_iterator i = tree->leaves.begin(),
       i_end = tree->leaves.end(); i != i_end; ++i)
  {
    property const &p = i->first;
    if (!i->second || !is_defined(p.bnd()) || is_bounded(p.bnd())) continue;
    number u = upper(p.bnd());
    if (u == number::pos_inf && !p.real.real2()) {
      real_op const *o = boost::get<real_op const>(p.real.real());
      if (o && o->type == UOP_ABS) u = 0;
    }
    new_leaves.push_back(property_tree::leave
      (property(p.real, interval(-u, -lower(p.bnd()))), false));
  }

  tree->leaves.insert(tree->leaves.end(), new_leaves.begin(), new_leaves.end());
  new_leaves.clear();
  typedef std::map< predicated_real, property > input_set;
  input_set inputs;

  // register approximates, and intersects properties with common reals
  for (std::vector<property_tree::leave>::const_iterator i = tree->leaves.begin(),
       i_end = tree->leaves.end(); i != i_end; ++i)
  {
    if (i->second) {
      new_leaves.push_back(*i);
      continue;
    }
    property const &p = i->first;
    if (p.real.real2())
      register_approx(p.real.real(), p.real.real2());
    else
      check_approx(p.real.real());
    std::pair< input_set::iterator, bool > ib = inputs.insert(std::make_pair(p.real, p));
    if (!ib.second) // there was already a known range
      ib.first->second.intersect(p);
  }

  for (input_set::const_iterator i = inputs.begin(),
       i_end = inputs.end(); i != i_end; ++i)
  {
    interval const &bnd = i->second.bnd();
    // bail out early if there is an empty set on an input
    if (is_empty(bnd))
    {
      std::cerr << "Warning: the hypotheses on " << dump_real_short(i->first)
                << " are trivially contradictory, skipping.\n";
      return;
    }
    // locate variables appearing in bounded expressions
    if (is_bounded(bnd)) input_reals.insert(i->first);
    ctx.hyp.push_back(i->second);
  }

  tree->leaves = new_leaves;
  ctx.goals = tree;
}

static void delete_prop(ast_prop const *p) {
  switch (p->type) {
  case PROP_NOT:
    delete_prop(p->lhs);
    break;
  case PROP_AND:
  case PROP_OR:
  case PROP_IMPL:
    delete_prop(p->lhs);
    delete_prop(p->rhs);
    break;
  case PROP_ATOM:
    delete p->atom;
  }
  delete p;
}

static void check_unbound()
{
  real_set bound_variables;
  for (preal_set::const_iterator i = input_reals.begin(),
       i_end = input_reals.end(); i != i_end; ++i)
  {
    predicated_real const &r = *i;
    find_unknown_reals(bound_variables, r.real());
    if (r.real2()) find_unknown_reals(bound_variables, r.real2());
  }
  real_set s;
  std::set_difference(free_variables.begin(), free_variables.end(),
                      bound_variables.begin(), bound_variables.end(),
                      std::inserter(s, s.begin()));
  free_variables.swap(s);
  for(real_set::const_iterator i = free_variables.begin(), end = free_variables.end(); i != end; ++i) {
    ast_ident const *n = (*i)->name;
    assert(n);
    std::cerr << "Warning: " << n->name << " is a variable without definition, yet it is unbound.\n";
  }
}

extern context goal;

void generate_graph(ast_prop const *p)
{
  parse_property_tree(p, goal);
  std::cerr << dump_prop_tree(goal.goals) << '\n';
  if (warning_unbound_variable)
    check_unbound();
  free_variables.clear();
  delete_prop(p);
}

// 0: no rule, 1: a rule but a missing relation, 2: a rule
int test_rewriting(ast_real const *src, ast_real const *dst, std::string &res) {
  std::ostringstream info;
  for(rewriting_vect::const_iterator i = rewriting_rules.begin(),
      i_end = rewriting_rules.end(); i != i_end; ++i) {
    rewriting_rule const &rw = **i;
    ast_real_vect holders;
    if (!match(src, rw.src, holders)) continue;
    bool b = holders.size() >= 2 && (!holders[0] || !holders[1]);
    if (!match(dst, rw.dst, holders, true)) continue;
    for(pattern_excl_vect::const_iterator j = rw.excl.begin(),
        j_end = rw.excl.end(); j != j_end; ++j)
      if (rewrite(j->first, holders) == rewrite(j->second, holders)) goto next_rule;
    if (b) {
      assert(holders[0] && holders[1]);
      link_map::const_iterator k = approximates.find(holders[0]);
      if (k != approximates.end() && k->second.find(holders[1]) != k->second.end())
        goto found_rule;
      info << "  " << dump_real(holders[1]) << " ~ " << dump_real(holders[0]) << '\n';
    } else {
      found_rule:
      info.str(std::string());
      for(pattern_cond_vect::const_iterator j = rw.cond.begin(),
          j_end = rw.cond.end(); j != j_end; ++j) {
        info << "  " << dump_real(rewrite(j->real, holders));
        char const *ops[] = { " < ", " <= ", " > ", " >= ", " != " };
        if (j->type == COND_NZ) info << " != 0 ";
        else info << ops[j->type] << j->value;
        info << '\n';
      }
      res = info.str();
      return 2;
    }
    next_rule: ;
  }
  res = info.str();
  return !res.empty();
}
