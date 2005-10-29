#include <cassert>
#include <iostream>
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/property.hpp"

interval create_interval(ast_interval const &, bool widen);

typedef std::set< ast_real const * > real_set;
real_set free_variables, input_reals, output_reals;

extern bool warning_unbound_variable;

static property generate_property(ast_atom_bound const &p, bool goal) {
  property r(p.real);
  if (p.interval.lower) {
    assert(p.interval.upper);
    r.bnd() = create_interval(p.interval, goal);
  } else {
    if (!goal)
      { std::cerr << "Error: undefined intervals are reserved for conclusions.\n"; exit(1); }
    assert(!p.interval.upper);
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

static void generate_goal(property_vect &goal, ast_prop const *p) {
  switch (p->type) {
  case PROP_ATOM:
    goal.push_back(generate_property(*p->atom, true));
    break;
  case PROP_AND:
    generate_goal(goal, p->lhs);
    generate_goal(goal, p->rhs);
    break;
  case PROP_OR:
    { std::cerr << "Error: complex logical formulas not yet implemented.\n"; exit(1); }
  default:
    assert(false);
  }
}

std::vector< graph_t * > graphs;

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
        t.lhs[idl] = s.lhs[s.lhs.size() - 1];
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
  property_vect hyp;
  real_set inputs;
  for(ast_prop_vect::const_iterator i = s.lhs.begin(), end = s.lhs.end(); i != end; ++i) {
    ast_prop const *p = *i;
    assert(p && p->type == PROP_ATOM);
    ast_atom_bound const &atom = *p->atom;
    hyp.push_back(generate_property(atom, false));
    inputs.insert(atom.real);
    input_reals.insert(atom.real);
  }
  if (hyp.size() != inputs.size()) // we don't want to encounter: x in [0,2] /\ x in [1,3] -> ...
    { std::cerr << "Error: you don't want to have multiple hypotheses concerning the same real.\n"; exit(1); }
  if (s.rhs.size() != 1)
    { std::cerr << "Error: complex logical formulas not yet implemented.\n"; exit(1); }
  property_vect goal;
  generate_goal(goal, s.rhs[0]);
  graph_t *g = new graph_t(NULL, hyp, goal);
  graphs.push_back(g);
  for(property_vect::const_iterator i = goal.begin(), end = goal.end(); i != end; ++i)
    output_reals.insert(i->real.real());
}

void generate_graph(ast_prop const *p) {
  sequent s;
  s.rhs.push_back(p);
  parse_sequent(s, 0, 0);
  if (warning_unbound_variable) {
    for(real_set::const_iterator i = input_reals.begin(), end = input_reals.end(); i != end; ++i) {
      ast_real const *r = *i;
      free_variables.erase(r);
      real_op const *o = boost::get< real_op const >(r);
      if (!o) continue;
      if (o->type == UOP_ABS || o->fun && o->fun->type == UOP_ID) free_variables.erase(o->ops[0]);
    }
    for(real_set::const_iterator i = free_variables.begin(), end = free_variables.end(); i != end; ++i) {
      ast_ident const *n = (*i)->name;
      assert(n);
      std::cerr << "Warning: " << n->name << " is a variable without definition, yet it is unbound.\n";
    }
  }
  free_variables.clear();
}
