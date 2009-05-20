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

static bool is_positive(ast_prop const *p) {
  switch (p->type) {
  case PROP_ATOM:	return true;
  case PROP_IMPL:
  case PROP_NOT:	return false;
  case PROP_AND:
  case PROP_OR:		break;
  }
  return is_positive(p->lhs) && is_positive(p->rhs);
}

static void generate_goal(property_tree &tree, ast_prop const *p)
{
  switch (p->type) {
  case PROP_ATOM:
    tree->leaves.push_back(generate_property(*p->atom, true));
    break;
  case PROP_AND:
  case PROP_OR: {
    property_tree *dst = &tree;
    if (tree->conjonction != (p->type == PROP_AND)) {
      tree->subtrees.push_back(new property_tree::data(p->type == PROP_AND));
      dst = &tree->subtrees.back();
    }
    generate_goal(*dst, p->lhs);
    generate_goal(*dst, p->rhs);
    break; }
  default:
    assert(false);
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

struct sequent {
  ast_prop_vect lhs, rhs;
};

static void parse_sequent(sequent &s, unsigned idl, unsigned idr) {
  while (idl < s.lhs.size() || idr < s.rhs.size()) {
    while (idl < s.lhs.size()) {
      ast_prop const *p = s.lhs[idl];
      switch (p->type) {
      case PROP_NOT: {
        s.lhs[idl] = s.lhs[s.lhs.size() - 1];
        s.lhs.pop_back();
        s.rhs.push_back(p->lhs);
        break;
      }
      case PROP_AND: {
        s.lhs[idl] = p->lhs;
        s.lhs.push_back(p->rhs);
        break;
      }
      case PROP_OR: {
        sequent t = s;
        s.lhs[idl] = p->lhs;
        t.lhs[idl] = p->rhs;
        parse_sequent(t, idl, idr);
        break;
      }
      case PROP_IMPL: {
        sequent t = s;
        s.lhs[idl] = p->rhs;
        t.lhs[idl] = t.lhs[t.lhs.size() - 1];
        t.lhs.pop_back();
        t.rhs.push_back(p->lhs);
        parse_sequent(t, idl, idr);
        break;
      }
      case PROP_ATOM:
        ++idl;
      }
    }
    while (idr < s.rhs.size()) {
      ast_prop const *p = s.rhs[idr];
      if (p->type == PROP_ATOM || (p->type == PROP_AND && is_positive(p))) { ++idr; continue; }
      switch (p->type) {
      case PROP_NOT: {
        s.rhs[idr] = s.rhs[s.rhs.size() - 1];
        s.rhs.pop_back();
        s.lhs.push_back(p->lhs);
        break;
      }
      case PROP_AND: {
        sequent t = s;
        s.rhs[idr] = p->lhs;
        t.rhs[idr] = p->rhs;
        parse_sequent(t, idl, idr);
        break;
      }
      case PROP_OR: {
        s.rhs[idr] = p->lhs;
        s.rhs.push_back(p->rhs);
        break;
      }
      case PROP_IMPL: {
        s.rhs[idr] = p->rhs;
        s.lhs.push_back(p->lhs);
        break;
      }
      default:
        assert(false);
      }
    }
  }

  // for any goal x>=b or x<=b, add the converse inequality as a hypothesis
  for (ast_prop_vect::const_iterator i = s.rhs.begin(),
       i_end = s.rhs.end(); i != i_end; ++i)
  {
    ast_prop const *p = *i;
    ast_atom_bound const &atom = *p->atom;
    if (p->type != PROP_ATOM || !atom.lower == !atom.upper) continue;
    s.lhs.push_back(new ast_prop(new ast_atom_bound(atom.real, atom.upper, atom.lower)));
  }

  // register approximates, and intersects properties with common reals
  typedef std::map< predicated_real, property > input_set;
  input_set inputs;
  for (ast_prop_vect::const_iterator i = s.lhs.begin(),
       i_end = s.lhs.end(); i != i_end; ++i)
  {
    ast_prop const *p = *i;
    assert(p && p->type == PROP_ATOM);
    ast_atom_bound const &atom = *p->atom;
    if (atom.real2)
      register_approx(atom.real, atom.real2);
    else
      check_approx(atom.real);
    property q = generate_property(atom, false);
    std::pair< input_set::iterator, bool > ib = inputs.insert(std::make_pair(q.real, q));
    if (!ib.second) // there was already a known range
      ib.first->second.intersect(q);
  }

  context ctxt;
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
    if (is_bounded(bnd))
      input_reals.insert(i->first);
    ctxt.hyp.push_back(i->second);
  }

  ctxt.goals = new
    property_tree::data(s.rhs.size() == 1 && s.rhs[0]->type != PROP_OR);
  for (ast_prop_vect::const_iterator i = s.rhs.begin(),
       i_end = s.rhs.end(); i != i_end; ++i)
  {
    generate_goal(ctxt.goals, *i);
  }
  contexts.push_back(ctxt);
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

void generate_graph(ast_prop const *p) {
  sequent s;
  s.rhs.push_back(p);
  parse_sequent(s, 0, 0);
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
