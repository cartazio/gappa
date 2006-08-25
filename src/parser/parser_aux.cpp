#include <cassert>
#include <iostream>
#include <sstream>
#include "parser/ast.hpp"
#include "parser/pattern.hpp"
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
  if (p.lower || p.upper) {
    interval &bnd = r.bnd();
    bnd = create_interval(p.lower, p.upper, !goal);
    if (is_empty(bnd))
      { std::cerr << "Error: the range of " << dump_real(p.real) << " is an empty interval.\n"; exit(1); }
  } else if (!goal)
    { std::cerr << "Error: undefined intervals are restricted to conclusions.\n"; exit(1); }
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
  for(ast_prop_vect::const_iterator i = s.rhs.begin(), end = s.rhs.end(); i != end; ++i) {
    ast_prop const *p = *i;
    ast_atom_bound const &atom = *p->atom;
    if (p->type != PROP_ATOM || !atom.lower == !atom.upper) continue;
    s.lhs.push_back(new ast_prop(new ast_atom_bound(atom.real, atom.upper, atom.lower)));
  }
  typedef std::map< ast_real const *, property > input_set;
  input_set inputs;
  for(ast_prop_vect::const_iterator i = s.lhs.begin(), end = s.lhs.end(); i != end; ++i) {
    ast_prop const *p = *i;
    assert(p && p->type == PROP_ATOM);
    ast_atom_bound const &atom = *p->atom;
    if (real_op const *o = boost::get< real_op const >(atom.real)) {
      // look for an approx/accurate pair
      if (o->type == UOP_ABS) o = boost::get< real_op const >(o->ops[0]);
      ast_real const *r = NULL;
      if (o && o->type == BOP_DIV) {
        r = o->ops[1];
        o = boost::get< real_op const >(o->ops[0]);
      }
      if (o && o->type == BOP_SUB && (!r || r == o->ops[1])) {
        accurates[o->ops[0]].insert(o->ops[1]);
        approximates[o->ops[1]].insert(o->ops[0]);
      }
    }
    property q = generate_property(atom, false);
    std::pair< input_set::iterator, bool > ib = inputs.insert(std::make_pair(atom.real, q));
    if (!ib.second) // there was already a known range
      ib.first->second.intersect(q);
  }
  context ctxt;
  for(input_set::const_iterator i = inputs.begin(), end = inputs.end(); i != end; ++i) {
    interval const &bnd = i->second.bnd();
    if (is_empty(bnd))
      { std::cerr << "Warning: the hypotheses on " << dump_real(i->first) << " are trivially contradictory.\n"; exit(1); }
    if (is_bounded(bnd))
      input_reals.insert(i->first);
    ctxt.hyp.push_back(i->second);
  }
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

// 0: no rule, 1: a rule but a missing relation, 2: a rule
int test_rewriting(ast_real const *src, ast_real const *dst, std::string &res) {
  std::ostringstream info;
  for(rewriting_vect::const_iterator i = rewriting_rules.begin(),
      i_end = rewriting_rules.end(); i != i_end; ++i) {
    rewriting_rule const &rw = **i;
    ast_real_vect holders;
    if (!match(src, rw.src, holders)) continue;
    bool b = holders.size() >= 2 && (!holders[0] || !holders[1]);
    if (!match(dst, rw.dst, holders)) continue;
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
