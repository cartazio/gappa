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

namespace {

struct property_key {
  property_type type;
  variable *var;
  ast_real const *real; // only used for ABS and REL
  property_key(property const &p): type(p.type), var(p.var), real(p.type != PROP_BND ? p.real : NULL) {}
  bool operator<(property_key const &p) const {
    return type < p.type || (type == p.type && (var < p.var || (var == p.var && real < p.real)));
  }
  typedef std::map< property_key, interval > map;
};

} // anonymous namespace

struct node_modus: node {
  std::string name;
  node_modus(node *n, property const &p);
  node_modus(property const &p, node *n, node_vect const &nodes);
};

node_modus::node_modus(node *n, property const &p): node(MODUS) {
  res = p;
  if (p.type != PROP_BND && p.var->real == p.real) {
    assert(n == triviality);
    return;
  }
  if (n == triviality) {
    int idx = res.var->get_definition();
    assert(idx != -1);
    instruction &inst = program[idx];
    assert(!inst.fun);
    property h = res;
    h.var = inst.in[0];
    hyp.push_back(h);
    return;
  }
  insert_pred(n);
  hyp = n->hyp;
}


node_modus::node_modus(property const &p, node *n, node_vect const &nodes): node(MODUS) {
  res = p;
  insert_pred(n);
  property_key::map pmap, rmap;
  for(node_vect::const_iterator i = nodes.begin(), i_end = nodes.end(); i != i_end; ++i) {
    node *m = *i;
    if (m == triviality) continue;
    insert_pred(m);
    {
      property const &p = m->res;
      property_key pk = p;
      property_key::map::iterator pki = rmap.find(pk);
      if (pki != rmap.end())
        pki->second = intersect(pki->second, p.bnd);
      else
        rmap.insert(std::make_pair(pk, p.bnd));
    }
    for(property_vect::const_iterator j = m->hyp.begin(), j_end = m->hyp.end(); j != j_end; ++j) {
      property const &p = *j;
      property_key pk = p;
      property_key::map::iterator pki = pmap.find(pk);
      if (pki != pmap.end())
        pki->second = hull(pki->second, p.bnd);
      else
        pmap.insert(std::make_pair(pk, p.bnd));
    }
  }
  for(property_vect::const_iterator j = n->hyp.begin(), j_end = n->hyp.end(); j != j_end; ++j) {
    property const &p = *j;
    property_key pk = p;
    property_key::map::iterator pki = rmap.find(pk); // is the hypothesis a result?
    if (pki != rmap.end() && pki->second <= p.bnd) continue;
    pki = pmap.find(pk);
    if (pki != pmap.end())
      pki->second = hull(pki->second, p.bnd);
    else
      pmap.insert(std::make_pair(pk, p.bnd));
  }
  for(property_key::map::const_iterator pki = pmap.begin(), pki_end = pmap.end(); pki != pki_end; ++pki) {
    property_key const &pk = pki->first;
    if (pk.type != PROP_BND && pk.var->real == pk.real) {
      assert(contains_zero(pki->second));
      continue;
    }
    property p(pk.type);
    p.var = pk.var;
    p.real = pk.real;
    p.bnd = pki->second;
    hyp.push_back(p);
  }
}

namespace basic_proof {

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

interval const &compute_triviality(property_vect const &hyp, variable *v) {
  property bnd(PROP_BND);
  bnd.var = v;
  //if (node *n = graph->find_compatible_node(hyp, bnd)) return n->res.bnd;
  int i = hyp.find_compatible_property(bnd);
  if (i < 0) { static interval const not_defined; return not_defined; }
  return hyp[i].bnd;
}

node *generate_bound(property_vect const &hyp, property &res);
node *generate_error(property_vect const &hyp, property &res);

interval compute_bound(property_vect const &hyp, variable *v) {
  { interval const &res = compute_triviality(hyp, v);
    if (is_defined(res)) return res; }
  int idx = v->get_definition();
  if (idx == -1) return interval();
  instruction &inst = program[idx];
  if (!inst.fun) return compute_bound(hyp, inst.in[0]);
  int l = inst.in.size();
  boost::scoped_array< interval > ints_(new interval[l]);
  boost::scoped_array< interval const * > ints(new interval const *[l]);
  for(int i = 0; i < l; ++i) {
    ints_[i] = compute_bound(hyp, inst.in[i]);
    if (!(is_defined(ints_[i]))) return interval();
    ints[i] = &ints_[i];
  }
  return (*inst.fun->bnd_comp->compute)(ints.get());
}

node *generate_bound(property_vect const &hyp, property &res) {
  assert(res.type == PROP_BND);
  if (node *n = generate_triviality(hyp, res)) return n;
  // std::cout << res.var->name->name << " in " << res.bnd << std::endl;
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (!inst.fun) {
    variable *v = res.var;
    res.var = inst.in[0];
    node *n = generate_bound(hyp, res);
    if (!n) return NULL;
    res.var = v;
    return new node_modus(n, res);
  }
  int l = inst.in.size();
  node_vect nodes(l);
  boost::scoped_array< property > props(new property[l]);
  boost::scoped_array< interval const * > ints(new interval const *[l]);
  for(int i = 0; i < l; ++i) {
    props[i].type = PROP_BND;
    props[i].var = inst.in[i];
    if (!(nodes[i] = generate_bound(hyp, props[i]))) return NULL;
    ints[i] = &props[i].bnd;
  }
  interval bnd = (*inst.fun->bnd_comp->compute)(ints.get());
  if (!is_defined(bnd) || !(bnd <= res.bnd)) return NULL;
  res.bnd = bnd;
  node *n = (*inst.fun->bnd_comp->generate)(props.get(), res);
  assert(n);
  return new node_modus(res, n, nodes);
}

node *generate_error_forced(property_vect const &hyp, property &res) {
  assert(res.type == PROP_ABS || res.type == PROP_REL);
  if (node *n = generate_triviality(hyp, res)) return n;
  /*{ static char const *type[] = { "ABS", "REL" };
    std::cout << type[res.error] << '(' << res.var->name->name << ", ...) in " << res.err << std::endl; }*/
  if (res.var->real == res.real) {
    if (!contains_zero(res.bnd)) return NULL;
    res.bnd = interval_real();
    return triviality;
  }
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (!inst.fun) {
    variable *v = res.var;
    res.var = inst.in[0];
    node *n = generate_error(hyp, res);
    if (!n) return NULL;
    res.var = v;
    return new node_modus(n, res);
  }
  real_op const *op = boost::get< real_op const >(res.real);
  if (!op || op->type != inst.fun->type) return NULL;
  node *n = NULL;
  node_vect nodes;
  for(error_computation const *m = inst.fun->err_comp; m->res.var != 0; ++m) {
    if (m->res.var != -1) continue; // TODO
    if (!(m->res.type == HYP_ABS && res.type == PROP_ABS || m->res.type == HYP_REL && res.type == PROP_REL)) continue;
    graph_layer layer;
    bool good = true;
    int l = 0;
    for(hypothesis_constraint const *c = m->constraints; c->var != 0; ++c) ++l;
    nodes.clear();
    boost::scoped_array< property > props(new property[l]);
    boost::scoped_array< interval const * > ints(new interval const *[l]);
    for(int i = 0; i < l; ++i) {
      hypothesis_constraint const *c = &m->constraints[i];
      variable *v = (c->var < 0) ? inst.out[-1 - c->var] : inst.in[c->var - 1] ;
      node *nn;
      property &p = props[i];
      p.var = v;
      if (c->type == HYP_BND || c->type == HYP_SNG) {
        p.type = PROP_BND;
        if (!(nn = generate_bound(hyp, p))) { good = false; break; }
        if (c->type == HYP_SNG && !is_singleton(p.bnd)) { good = false; break; }
      } else if (c->type == HYP_ABS || c->type == HYP_REL) {
        p.type = c->type == HYP_ABS ? PROP_ABS : PROP_REL;
        assert(c->var >= 1);
        p.real = op->ops[c->var - 1];
        if (!(nn = generate_error(hyp, p))) { good = false; break; }
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

node *generate_error(property_vect const &hyp, property &res) {
  assert(res.type == PROP_ABS || res.type == PROP_REL);
  property res2 = res;
  {
    graph_layer layer;
    node *n = generate_error_forced(hyp, res);
    if (n) { layer.flatten(); return n; }
  }
  property bnd(PROP_BND);
  bnd.var = res2.var;
  node *nb = generate_bound(hyp, bnd);
  if (!nb) return NULL;
  property err(res2.type == PROP_ABS ? PROP_REL : PROP_ABS);
  err.var = res2.var;
  err.real = res2.real;
  node *ne = generate_error_forced(hyp, err);
  if (!ne) return NULL;
  res = res2;
  if (res2.type == PROP_ABS)
    res.bnd = static_cast< interval_real const & >(err.bnd) * to_real(bnd.bnd);
  else if (!is_zero(err.bnd)) {
    if (contains_zero(bnd.bnd)) return NULL;
    res.bnd = static_cast< interval_real const & >(err.bnd) / to_real(bnd.bnd);
  }
  if (!(res.bnd <= res2.bnd)) return NULL;
  node_vect nodes;
  nodes.push_back(nb);
  nodes.push_back(ne);
  property hyps[2] = { bnd, err };
  return new node_modus(res, new node_theorem(2, hyps, res, "relabs"), nodes);
}

} // namespace basic_proof

node *generate_basic_proof(property_vect const &hyp, property const &res) {
  property res2 = res;
  node *n;
  if (res.type == PROP_BND)
    n = basic_proof::generate_bound(hyp, res2);
  else
    n = basic_proof::generate_error(hyp, res2);
  return n;
}
