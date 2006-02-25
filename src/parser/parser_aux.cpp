#include <cassert>
#include <iostream>
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"

typedef std::set< ast_real const * > real_set;
real_set free_variables, input_reals, output_reals;

interval create_interval(ast_number const *, ast_number const *, bool);
void find_unknown_reals(real_set &, ast_real const *);

extern bool warning_unbound_variable;

static property generate_property(ast_atom_bound const &p, bool goal) {
  property r(p.real);
  output_reals.insert(p.real);
  if (p.lower || p.upper) r.bnd() = create_interval(p.lower, p.upper, goal);
  else if (!goal) { std::cerr << "Error: undefined intervals are restricted to conclusions.\n"; exit(1); }
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

static void generate_goal(property_tree &tree, ast_prop const *p) {
  if (tree.empty())
    tree = new property_tree::data(p->type != PROP_OR);
  else
    tree.unique();
  switch (p->type) {
  case PROP_ATOM:
    tree->leafs.push_back(generate_property(*p->atom, true));
    break;
  case PROP_AND:
  case PROP_OR: {
    property_tree tmp, *dst;
    if (tree->conjonction != (p->type == PROP_AND)) {
      tmp = new property_tree::data(p->type == PROP_AND);
      tree->subtrees.push_back(tmp);
      dst = &tmp;
    } else dst = &tree;
    generate_goal(*dst, p->lhs);
    generate_goal(*dst, p->rhs);
    break; }
  default:
    assert(false);
  }
}

struct sequent {
  ast_prop_vect lhs, rhs;
  std::vector< int > deps;
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
        sequent t;
        t.lhs = s.lhs;
        t.rhs = s.rhs;
        s.lhs[idl] = p->rhs;
        t.lhs[idl] = s.lhs[s.lhs.size() - 1];
        t.lhs.pop_back();
        t.rhs.push_back(p->lhs);
        parse_sequent(t, idl, idr);
        s.deps.push_back(contexts.size() - 1);
        break;
      }
      case PROP_ATOM:
        ++idl;
      }
    }
    while (idr < s.rhs.size()) {
      ast_prop const *p = s.rhs[idr];
      if (is_positive(p)) { ++idr; continue; }
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
  context ctxt;
  real_set inputs;
  for(ast_prop_vect::const_iterator i = s.lhs.begin(), end = s.lhs.end(); i != end; ++i) {
    ast_prop const *p = *i;
    assert(p && p->type == PROP_ATOM);
    ast_atom_bound const &atom = *p->atom;
    ctxt.hyp.push_back(generate_property(atom, false));
    inputs.insert(atom.real);
    if (atom.lower && atom.upper) input_reals.insert(atom.real);
  }
  if (ctxt.hyp.size() != inputs.size()) // we don't want to encounter: x in [0,2] /\ x in [1,3] -> ...
    { std::cerr << "Error: you don't want to have multiple hypotheses concerning the same real.\n"; exit(1); }
  if (s.rhs.size() == 1)
    generate_goal(ctxt.goals, s.rhs[0]);
  else if (!s.rhs.empty()) {
    ctxt.goals = new property_tree::data(false);
    for(ast_prop_vect::const_iterator i = s.rhs.begin(), end = s.rhs.end(); i != end; ++i)
      generate_goal(ctxt.goals, *i);
  }
  ctxt.deps = s.deps;
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

static void check_unbound() {
  real_set bound_variables;
  for(real_set::const_iterator i = input_reals.begin(), end = input_reals.end(); i != end; ++i)
    find_unknown_reals(bound_variables, *i);
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
