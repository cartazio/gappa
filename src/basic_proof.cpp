#include <algorithm>
#include <iostream>
#include <map>
#include <boost/scoped_array.hpp>
#include "basic_proof.hpp"
#include "proof_graph.hpp"
#include "program.hpp"
#include "ast.hpp"
#include "numbers/interval_ext.hpp"
#include "function.hpp"

/*
Trivialities are emitted when the result of a basic proof directly
matches one of the hypotheses. They all are the same node, and it does
not convey any interesting information. Consequently the result is
carried through the reference parameter. All the trivialities should be
destroyed by modus or assignation.
*/

node *triviality = new node(OTHER);

struct node_theorem: node {
  char const *name;
  node_theorem(int nb, property const *h, property const &p, char const *n): node(THEOREM), name(n) {
    res = p;
    for(int i = 0; i < nb; ++i) hyp.push_back(h[i]);
  }
};

struct node_modus: node {
  std::string name;
  node_modus(node *n, property const &p);
  node_modus(property const &p, node *n, node_vect const &nodes);
};

node_modus::node_modus(node *n, property const &p): node(MODUS) {
  res = p;
  if (n == triviality) {
    if (error_bound const *e = boost::get< error_bound const >(p.real)) {
      assert(e->var->real == e->real);
    } else {
      variable const *v = res.real->get_variable();
      assert(v);
      instruction *inst = v->inst;
      assert(inst && !inst->fun);
      property h = res;
      h.real = inst->in[0]->real;
      hyp.push_back(h);
    }
    return;
  }
  insert_pred(n);
  hyp = n->hyp;
}

node_modus::node_modus(property const &p, node *n, node_vect const &nodes): node(MODUS) {
  res = p;
  insert_pred(n);
  typedef std::map< ast_real const *, interval > property_map;
  property_map pmap, rmap;
  for(node_vect::const_iterator i = nodes.begin(), i_end = nodes.end(); i != i_end; ++i) {
    node *m = *i;
    if (m == triviality) continue;
    insert_pred(m);
    {
      property const &p = m->res;
      property_map::iterator pki = rmap.find(p.real);
      if (pki != rmap.end())
        pki->second = intersect(pki->second, p.bnd);
      else
        rmap.insert(std::make_pair(p.real, p.bnd));
    }
    for(property_vect::const_iterator j = m->hyp.begin(), j_end = m->hyp.end(); j != j_end; ++j) {
      property const &p = *j;
      property_map::iterator pki = pmap.find(p.real);
      if (pki != pmap.end())
        pki->second = hull(pki->second, p.bnd);
      else
        pmap.insert(std::make_pair(p.real, p.bnd));
    }
  }
  for(property_vect::const_iterator j = n->hyp.begin(), j_end = n->hyp.end(); j != j_end; ++j) {
    property const &p = *j;
    property_map::iterator pki = rmap.find(p.real); // is the hypothesis a result?
    if (pki != rmap.end() && pki->second <= p.bnd) continue;
    pki = pmap.find(p.real);
    if (pki != pmap.end())
      pki->second = hull(pki->second, p.bnd);
    else
      pmap.insert(std::make_pair(p.real, p.bnd));
  }
  for(property_map::const_iterator pki = pmap.begin(), pki_end = pmap.end(); pki != pki_end; ++pki) {
    if (error_bound const *e = boost::get< error_bound const >(p.real)) {
      if (e->var->real == e->real) {
        assert(contains_zero(pki->second));
        continue;
      }
    }
    property p(pki->first, pki->second);
    hyp.push_back(p);
  }
}

node *generate_triviality(property_vect const &hyp, property &res) {
  if (node *n = graph->find_compatible_node(hyp, res)) {
    res = n->res;
    return n;
  }
  int i = hyp.find_compatible_property(res);
  if (i < 0) return NULL;
  res = hyp[i];
  return triviality;
}

interval const &compute_triviality(property_vect const &hyp, ast_real const *r) {
  property bnd(r);
  //if (node *n = graph->find_compatible_node(hyp, bnd)) return n->res.bnd;
  int i = hyp.find_compatible_property(bnd);
  if (i < 0) { static interval const not_defined; return not_defined; }
  return hyp[i].bnd;
}

/*
interval compute_bound(property_vect const &hyp, ast_real const *r) {
  { interval const &res = compute_triviality(hyp, r);
    if (is_defined(res)) return res; }
  if (variable const *v = r->get_variable()) {
    instruction *inst = v->inst;
    if (!inst) return interval();
    if (!inst->fun) return compute_bound(hyp, inst->in[0]->real);
    int l = inst->in.size();
    boost::scoped_array< interval > ints_(new interval[l]);
    boost::scoped_array< interval const * > ints(new interval const *[l]);
    for(int i = 0; i < l; ++i) {
      ints_[i] = compute_bound(hyp, inst->in[i]->real);
      if (!(is_defined(ints_[i]))) return interval();
      ints[i] = &ints_[i];
    }
    return (*inst->fun->bnd_comp->compute)(ints.get());
  } else
    return interval();
}
*/

node *generate_trans_bound(property_vect const &hyp, property &res) {
  variable const *v = res.real->get_variable();
  assert(v);
  instruction *inst = v->inst;
  assert(inst && !inst->fun);
  res.real = inst->in[0]->real;
  node *n = handle_proof(hyp, res);
  if (!n) return NULL;
  res.real = v->real;
  return new node_modus(n, res);
}

node *generate_basic_bound(property_vect const &hyp, property &res) {
  variable const *v = res.real->get_variable();
  assert(v);
  instruction *inst = v->inst;
  assert(inst && inst->fun);
  int l = inst->in.size();
  node_vect nodes(l);
  boost::scoped_array< property > props(new property[l]);
  boost::scoped_array< interval const * > ints(new interval const *[l]);
  for(int i = 0; i < l; ++i) {
    props[i].real = inst->in[i]->real;
    if (!(nodes[i] = handle_proof(hyp, props[i]))) return NULL;
    ints[i] = &props[i].bnd;
  }
  interval bnd = (*inst->fun->bnd_comp->compute)(ints.get());
  if (!is_defined(bnd) || !(bnd <= res.bnd)) return NULL;
  res.bnd = bnd;
  node *n = (*inst->fun->bnd_comp->generate)(props.get(), res);
  assert(n);
  return new node_modus(res, n, nodes);
}

node *generate_refl_error(property_vect const &hyp, property &res) {
  error_bound const *e = boost::get< error_bound const >(res.real);
  assert(e && e->var->real == e->real);
  if (!contains_zero(res.bnd)) return NULL;
  res.bnd = interval_real();
  return triviality;
}

node *generate_trans_error(property_vect const &hyp, property &res) {
  error_bound const *e = boost::get< error_bound const >(res.real);
  assert(e);
  instruction *inst = e->var->inst;
  assert(inst && !inst->fun);
  error_bound e2(e->type, inst->in[0], e->real);
  ast_real const *r = res.real;
  res.real = normalize(ast_real(e2));
  node *n = handle_proof(hyp, res);
  if (!n) return NULL;
  res.real = r;
  return new node_modus(n, res);
}

node *generate_basic_error(property_vect const &hyp, property &res) {
  error_bound const *e = boost::get< error_bound const >(res.real);
  assert(e);
  instruction *inst = e->var->inst;
  assert(inst && inst->fun);
  real_op const *op = boost::get< real_op const >(e->real);
  if (!op || op->type != inst->fun->type) return NULL;
  node *n = NULL;
  node_vect nodes;
  for(error_computation const *m = inst->fun->err_comp; m->res.var != 0; ++m) {
    if (m->res.var != -1) continue; // TODO
    if (!(m->res.type == HYP_ABS && e->type == ERROR_ABS || m->res.type == HYP_REL && e->type == ERROR_REL)) continue;
    graph_layer layer;
    bool good = true;
    int l = 0;
    for(hypothesis_constraint const *c = m->constraints; c->var != 0; ++c) ++l;
    nodes.clear();
    boost::scoped_array< property > props(new property[l]);
    boost::scoped_array< interval const * > ints(new interval const *[l]);
    for(int i = 0; i < l; ++i) {
      hypothesis_constraint const *c = &m->constraints[i];
      variable *v = (c->var < 0) ? inst->out[-1 - c->var] : inst->in[c->var - 1] ;
      node *nn;
      property &p = props[i];
      if (c->type == HYP_BND || c->type == HYP_SNG) {
        p.real = v->real;
        if (!(nn = handle_proof(hyp, p))) { good = false; break; }
        if (c->type == HYP_SNG && !is_singleton(p.bnd)) { good = false; break; }
      } else if (c->type == HYP_ABS || c->type == HYP_REL) {
        assert(c->var >= 1);
        error_bound ep(c->type == HYP_ABS ? ERROR_ABS : ERROR_REL, v, op->ops[c->var - 1]);
        p.real = normalize(ast_real(ep));
        if (!(nn = handle_proof(hyp, p))) { good = false; break; }
      } else assert(false);
      ints[i] = &p.bnd;
      nodes.push_back(nn);
    }
    if (!good) continue;
    interval bnd = (*m->compute)(ints.get());
    if (!is_defined(bnd) || !(bnd <= res.bnd)) continue;
    res.bnd = bnd;
    n = (*m->generate)(&props[0], res);
    layer.flatten();
    break;
  }
  if (!n) return NULL;
  return new node_modus(res, n, nodes);
}

node *generate_relabs(property_vect const &hyp, property &res) {
  property res2 = res;
  error_bound const *e = boost::get< error_bound const >(res2.real);
  assert(e);
  property bnd(e->var->real);
  node *nb = handle_proof(hyp, bnd);
  if (!nb) return NULL;
  property err(normalize(ast_real(error_bound(e->type == ERROR_ABS ? ERROR_REL : ERROR_ABS, e->var, e->real))));
  node *ne = handle_proof(hyp, err);
  if (!ne) return NULL;
  res = res2;
  if (e->type == ERROR_ABS)
    res.bnd = static_cast< interval_real const & >(err.bnd) * to_real(bnd.bnd);
  else if (!is_zero(err.bnd)) {
    if (contains_zero(bnd.bnd)) return NULL;
    res.bnd = static_cast< interval_real const & >(err.bnd) / to_real(bnd.bnd);
  } else
    res.bnd = interval();
  if (!(res.bnd <= res2.bnd)) return NULL;
  node_vect nodes;
  nodes.push_back(nb);
  nodes.push_back(ne);
  property hyps[2] = { bnd, err };
  return new node_modus(res, new node_theorem(2, hyps, res, "relabs"), nodes);
}

void add_scheme(ast_real *r, node *(*f)(property_vect const &, property &)) {
  for(proof_scheme const *scheme = r->scheme, *prev = NULL; scheme != NULL;
      prev = scheme, scheme = scheme->next)
    if (scheme->generate_proof == f) {
      if (!prev) return;
      const_cast< proof_scheme * >(prev)->next = scheme->next;
      const_cast< proof_scheme * >(scheme)->next = r->scheme;
      r->scheme = scheme;
      return;
    }
  proof_scheme *s = new proof_scheme;
  s->generate_proof = f;
  s->next = r->scheme;
  r->scheme = s;
}

void add_basic_scheme(ast_real *r) {
  if (variable *v = r->get_variable()) {
    if (v->inst)
      if (v->inst->fun)
        add_scheme(r, &generate_basic_bound);
      else
        add_scheme(r, &generate_trans_bound);
  } else if (error_bound const *e = boost::get< error_bound const >(r)) {
    add_scheme(r, &generate_relabs);
    if (e->var->inst)
      if (e->var->inst->fun)
        add_scheme(r, &generate_basic_error);
      else
        add_scheme(r, &generate_trans_error);
    if (e->var->real == e->real)
      add_scheme(r, &generate_refl_error);
  }
}

node *handle_proof(property_vect const &hyp, property &res) {
  typedef std::vector< proof_scheme const * > scheme_stack;
  static scheme_stack st;
  if (node *n = generate_triviality(hyp, res)) return n;
  for(proof_scheme const *scheme = res.real->scheme; scheme != NULL; scheme = scheme->next) {
    if (std::count(st.begin(), st.end(), scheme) >= 3) continue; // BLI
    st.push_back(scheme);
    graph_layer layer;
    property res2 = res;
    node *n = (*scheme->generate_proof)(hyp, res);
    st.pop_back();
    if (n) {
      layer.flatten();
      return n;
    }
    res = res2;
  }
  return NULL;
}
