#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "proofs/basic_proof.hpp"
#include "proofs/schemes.hpp"

std::vector< scheme_factory const * > scheme_register::factories;

struct scheme_factory_wrapper: scheme_factory {
  typedef scheme_register::scheme_factory_fun scheme_factory_fun;
  scheme_factory_fun fun;
  scheme_factory_wrapper(scheme_factory_fun f): fun(f) {}
  virtual proof_scheme *operator()(ast_real const *r) const { return (*fun)(r); }
};

scheme_register::scheme_register(scheme_factory_fun f) {
  factories.push_back(new scheme_factory_wrapper(f));
}

scheme_register::scheme_register(scheme_factory const *f) {
  factories.push_back(f);
}

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
  // put a dummy yes_scheme as a marker for the current real
  r->scheme = new yes_scheme;
  std::vector< proof_scheme * > schemes;
  typedef scheme_register all_schemes;
  for(all_schemes::iterator i = all_schemes::begin(), i_end = all_schemes::end(); i != i_end; ++i) {
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
    if (in_hyp || graph->has_compatible_hypothesis(r)) {
      // keep the dummy yes_scheme as a marker for an already done real
      // without any non-trivial scheme
      return true;
    }
    delete r->scheme;
    // put a dummy no_scheme to mark this real as unusable
    r->scheme = new no_scheme;
    return false;
  }
  delete r->scheme;
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
  bool optimal;
  node *triviality_node = generate_triviality(hyp, res, optimal);
  if (optimal) return triviality_node;
  proof_scheme const *lower_scheme = NULL, *upper_scheme = NULL;
  interval best;
  bool lower_strict = triviality_node, upper_strict = triviality_node;
  number lower_best, upper_best;
  if (is_defined(res.bnd)) {
    lower_best = lower(res.bnd);
    upper_best = upper(res.bnd);
  } else {
    lower_best = number::neg_inf;
    upper_best = number::pos_inf;
  }
  for(proof_scheme const *scheme = res.real->scheme; scheme != NULL; scheme = scheme->next) {
    if (std::count(st.begin(), st.end(), scheme) >= 1) continue; // BLI
    st.push_back(scheme);
    { // lower bound search
      property res2(res.real, interval(lower_best, number::pos_inf));
      graph_layer layer(hyp);
      node *n = scheme->generate_proof(hyp, res2);
      if (n) {
        number const &lower_res = lower(res2.bnd);
        if (lower_res > lower_best || (!lower_strict && lower_res >= lower_best)) {
          lower_scheme = scheme;
          lower_best = lower_res;
          lower_strict = true;
        }
        number const &upper_res = upper(res2.bnd);
        if (upper_res < upper_best || (!upper_strict && upper_res <= upper_best)) {
          upper_scheme = scheme;
          upper_best = upper_res;
          upper_strict = true;
          st.pop_back();
          continue;
        }
      }
    }
    { // in case we didn't find a suitable upper bound because of the lower
      // bound restriction or because of the infinite upper bound
      property res2(res.real, interval(number::neg_inf, upper_best));
      graph_layer layer(hyp);
      node *n = scheme->generate_proof(hyp, res2);
      if (n) {
        number const &upper_res = upper(res2.bnd);
        if (upper_res < upper_best || (!upper_strict && upper_res <= upper_best)) {
          upper_scheme = scheme;
          upper_best = upper_res;
          upper_strict = true;
        }
      }
    }
    st.pop_back();
  }
  if (!(triviality_node || (lower_scheme && upper_scheme))) return NULL;
  if (lower_scheme == upper_scheme) { // catch also triviality_node
    node *n = triviality_node;
    if (lower_scheme) {
      res.bnd = interval(lower_best, upper_best);
      st.push_back(lower_scheme);
      n = lower_scheme->generate_proof(hyp, res);
      st.pop_back();
      assert(n);
    }
    if (n != triviality && graph->cache_dom == hyp)
      graph->cache[res.real] = n;
    return n;
  }
  property res1(res.real), res2(res.real);
  node *n1, *n2;
  if (lower_scheme) {
    res1.bnd = interval(lower_best, number::pos_inf);
    st.push_back(lower_scheme);
    n1 = lower_scheme->generate_proof(hyp, res1);
    st.pop_back();
    assert(n1);
  } else {
    res1.bnd = res.bnd;
    n1 = triviality_node;
  }
  if (upper_scheme) {
    res2.bnd = interval(number::neg_inf, upper_best);
    st.push_back(upper_scheme);
    n2 = upper_scheme->generate_proof(hyp, res2);
    st.pop_back();
    assert(n2);
  } else {
    res2.bnd = res.bnd;
    n2 = triviality_node;
  }
  res.bnd = interval(lower(res1.bnd), upper(res2.bnd));
  node_vect nodes;
  nodes.push_back(n1);
  nodes.push_back(n2);
  property hyps[2] = { res1, res2 };
  node *n = new node_modus(res, new node_theorem(2, hyps, res, "intersect"), nodes);
  if (graph->cache_dom == hyp)
    graph->cache[res.real] = n;
  return n;
}
