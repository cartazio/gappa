#include "ast.hpp"
#include "basic_proof.hpp"
#include "function.hpp"
#include "program.hpp"
#include "proof_graph.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/round.hpp"

#include <algorithm>
#include <iostream>
#include <map>
#include <boost/scoped_array.hpp>

/*
Trivialities are emitted when the result of a basic proof directly
matches one of the hypotheses. They all are the same node, and it does
not convey any interesting information. Consequently the result is
carried through the reference parameter. All the trivialities should be
destroyed by modus or assignation.
*/

node *triviality = (node *)1;

node_theorem::node_theorem(int nb, property const *h, property const &p, std::string n): node(THEOREM), name(n) {
  res = p;
  for(int i = 0; i < nb; ++i) hyp.push_back(h[i]);
}

struct node_modus: node {
  std::string name;
  node_modus(node *n, property const &p);
  node_modus(property const &p, node *n, node_vect const &nodes);
};

node_modus::node_modus(node *n, property const &p): node(MODUS) {
  res = p;
  if (n == triviality) {
    /*
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
    */
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
    /*
    if (error_bound const *e = boost::get< error_bound const >(p.real)) {
      if (e->var->real == e->real) {
        assert(contains_zero(pki->second));
        continue;
      }
    }
    */
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

/*
interval const &compute_triviality(property_vect const &hyp, ast_real const *r) {
  property bnd(r);
  //if (node *n = graph->find_compatible_node(hyp, bnd)) return n->res.bnd;
  int i = hyp.find_compatible_property(bnd);
  if (i < 0) { static interval const not_defined; return not_defined; }
  return hyp[i].bnd;
}

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

/*
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
  res.bnd = zero();
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
    res.bnd = err.bnd * bnd.bnd;
  else if (!is_zero(err.bnd)) {
    if (contains_zero(bnd.bnd)) return NULL;
    res.bnd = err.bnd / bnd.bnd;
  } else
    res.bnd = zero();
  if (!(res.bnd <= res2.bnd)) return NULL;
  node_vect nodes;
  nodes.push_back(nb);
  nodes.push_back(ne);
  property hyps[2] = { bnd, err };
  return new node_modus(res, new node_theorem(2, hyps, res, "relabs"), nodes);
}
*/

struct scheme_register {
  typedef proof_scheme *(*scheme_factory)(ast_real const *);
  typedef std::vector< scheme_factory >::const_iterator factory_iterator;
  static std::vector< scheme_factory > factories;
  //template< class T > scheme_register() { factories.push_back(&T::factory); }
  scheme_register(scheme_factory f) { factories.push_back(f); }
};

std::vector< scheme_register::scheme_factory > scheme_register::factories;

// ABSOLUTE_ERROR
struct absolute_error_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *absolute_error_scheme::generate_proof(property_vect const &hyp, property &res) const {
  real_op const *o = boost::get< real_op const >(res.real);
  assert(o && o->type == BOP_SUB);
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  assert(rr && o->ops[0] == rr->rounded);
  property res2(rr->rounded);
  node *n = handle_proof(hyp, res2);
  if (!n) return NULL;
  std::string name;
  interval bnd = rr->rounding->error(res2.bnd, name);
  if (!(bnd <= res.bnd)) return NULL;
  res.bnd = bnd;
  node_vect nodes;
  nodes.push_back(n);
  return new node_modus(res, new node_theorem(1, &res2, res, name), nodes);
}

ast_real_vect absolute_error_scheme::needed_reals(ast_real const *real) const {
  real_op const *o = boost::get< real_op const >(real);
  assert(o && o->type == BOP_SUB);
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  assert(rr && o->ops[0] == rr->rounded);
  return ast_real_vect(1, rr->rounded);
}

proof_scheme *absolute_error_scheme::factory(ast_real const *r) {
  real_op const *o = boost::get< real_op const >(r);
  if (!o) return NULL;
  if (o->type != BOP_SUB) return NULL;
  rounded_real const *rr = boost::get< rounded_real const >(o->ops[1]);
  if (!rr || o->ops[0] != rr->rounded) return NULL;
  return new absolute_error_scheme;
}

scheme_register absolute_error_scheme_register(&absolute_error_scheme::factory);

// ROUNDING_BOUND
struct rounding_bound_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *rounding_bound_scheme::generate_proof(property_vect const &hyp, property &res) const {
  rounded_real const *r = boost::get< rounded_real const >(res.real);
  assert(r);
  property res2(r->rounded);
  node *n = handle_proof(hyp, res2);
  if (!n) return NULL;
  std::string name;
  interval bnd = r->rounding->bound(res2.bnd, name);
  if (!(bnd <= res.bnd)) return NULL;
  res.bnd = bnd;
  node_vect nodes;
  nodes.push_back(n);
  return new node_modus(res, new node_theorem(1, &res2, res, name), nodes);
}

ast_real_vect rounding_bound_scheme::needed_reals(ast_real const *real) const {
  rounded_real const *r = boost::get< rounded_real const >(real);
  assert(r);
  return ast_real_vect(1, r->rounded);
}

proof_scheme *rounding_bound_scheme::factory(ast_real const *r) {
  if (!boost::get< rounded_real const >(r)) return NULL;
  return new rounding_bound_scheme;
}

scheme_register rounding_bound_scheme_register(&rounding_bound_scheme::factory);

// COMPUTATION
struct computation_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const;
  static proof_scheme *factory(ast_real const *);
};

node *computation_scheme::generate_proof(property_vect const &hyp, property &res) const {
  real_op const *r = boost::get< real_op const >(res.real);
  assert(r);
  node_vect nodes;
  node *n = NULL;
  switch (r->ops.size()) {
  case 1: {
    assert(r->type == UOP_MINUS);
    property res1(r->ops[0]);
    node *n1 = handle_proof(hyp, res1);
    if (!n1) return NULL;
    res.bnd = -res1.bnd;
    nodes.push_back(n1);
    n = new node_theorem(1, &res1, res, "neg");
    break; }
  case 2: {
    property res1(r->ops[0]);
    node *n1 = handle_proof(hyp, res1);
    if (!n1) return NULL;
    interval const &i1 = res1.bnd;
    property res2(r->ops[1]);
    node *n2 = handle_proof(hyp, res2);
    if (!n2) return NULL;
    interval const &i2 = res2.bnd;
    char const *s = NULL;
    interval i;
    switch (r->type) {
    case BOP_ADD: i = i1 + i2; s = "add"; break;
    case BOP_SUB: i = i1 - i2; s = "sub"; break;
    case BOP_MUL: i = i1 * i2; s = "mul"; break;
    case BOP_DIV:
      if (contains_zero(i2)) return NULL;
      i = i1 / i2;
      s = "div";
      break;
    default:
      assert(false);
      return NULL;
    }
    if (!(i <= res.bnd)) return NULL;
    res.bnd = i;
    nodes.push_back(n1);
    nodes.push_back(n2);
    property hyps[2] = { res1, res2 };
    n = new node_theorem(2, hyps, res, s);
    break; }
  default:
    assert(false);
  }
  return new node_modus(res, n, nodes);
}

ast_real_vect computation_scheme::needed_reals(ast_real const *real) const {
  real_op const *r = boost::get< real_op const >(real);
  assert(r);
  return r->ops;
}

proof_scheme *computation_scheme::factory(ast_real const *r) {
  if (!boost::get< real_op const >(r)) return NULL;
  return new computation_scheme;
}

scheme_register computation_scheme_register(&computation_scheme::factory);

// NUMBER
struct number_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
  static proof_scheme *factory(ast_real const *);
};

interval create_interval(ast_interval const &, bool widen = true);

node *number_scheme::generate_proof(property_vect const &hyp, property &res) const {
  ast_number const *const *r = boost::get< ast_number const *const >(res.real);
  assert(r);
  ast_interval _i = { *r, *r };
  interval i = create_interval(_i);
  if (!(i <= res.bnd)) return NULL;
  res.bnd = i;
  return new node_theorem(0, NULL, res, "constant");
}

proof_scheme *number_scheme::factory(ast_real const *r) {
  if (!boost::get< ast_number const *const >(r)) return NULL;
  return new number_scheme;
}

scheme_register number_scheme_register(&number_scheme::factory);

// REWRITE
struct rewrite_scheme: proof_scheme {
  ast_real const *real;
  std::string name;
  rewrite_scheme(ast_real const *r, std::string const &n): real(r), name(n) {}
  virtual node *generate_proof(property_vect const &, property &) const;
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(1, real); }
  //static proof_scheme *factory(ast_real const *);
};

node *rewrite_scheme::generate_proof(property_vect const &hyp, property &res) const {
  property res2(real, res.bnd);
  node *n = handle_proof(hyp, res2);
  if (!n) return NULL;
  res.bnd = res2.bnd;
  node_vect nodes;
  nodes.push_back(n);
  return new node_modus(res, new node_theorem(1, &res2, res, name), nodes);
}

//scheme_register rewrite_scheme_register(&rewrite_scheme::factory);

//
struct no_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const { return NULL; }
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
};

struct yes_scheme: proof_scheme {
  virtual node *generate_proof(property_vect const &, property &) const { return NULL; }
  virtual ast_real_vect needed_reals(ast_real const *) const { return ast_real_vect(); }
};

bool generate_scheme_tree(property_vect const &hyp, ast_real const *r) {
  if (r->scheme) return !dynamic_cast< no_scheme const * >(r->scheme);
  { static yes_scheme dummy;
    r->scheme = &dummy; }
  std::vector< proof_scheme * > schemes;
  for(scheme_register::factory_iterator i = scheme_register::factories.begin(), i_end = scheme_register::factories.end();
      i != i_end; ++i) {
    proof_scheme *s = (**i)(r);
    if (!s) continue;
    ast_real_vect v = s->needed_reals(r);
    bool good = true;
    for(ast_real_vect::const_iterator j = v.begin(), j_end = v.end(); j != j_end; ++j) {
      good = generate_scheme_tree(hyp, *j);
      if (!good) break;
    }
    if (good)
      schemes.push_back(s);
    else
      delete s;
  }
  unsigned s = schemes.size();
  if (s == 0) {
    bool in_hyp = false;
    for(property_vect::const_iterator i = hyp.begin(), end = hyp.end(); i != end; ++i) {
      in_hyp = r == i->real;
      if (in_hyp) break;
    }
    if (in_hyp) return true;
    if (graph->has_compatible_hypothesis(r)) return true;
    static no_scheme dummy;
    r->scheme = &dummy;
    return false;
  }
  r->scheme = NULL;
  for(unsigned i = 0; i < s; ++i) {
    proof_scheme *p = schemes[i];
    p->next = r->scheme;
    r->scheme = p;
  }
  return true;
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
    node *n = scheme->generate_proof(hyp, res);
    st.pop_back();
    if (n) {
      layer.flatten();
      return n;
    }
    res = res2;
  }
  return NULL;
}
