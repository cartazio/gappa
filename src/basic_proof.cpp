#include "basic_proof.hpp"
#include "proof_graph.hpp"
#include "program.hpp"
#include "ast.hpp"
#include "interval.hpp"
#include <iostream>

namespace {

struct generator_theorem: generator {
  virtual node *do_it() { /* TODO */ return NULL; }
  generator_theorem(property const &p): generator(p) {}
};

struct generator_hypothesis: generator {
  virtual node *do_it() { /* TODO */ return NULL; }
  int idx;
  generator_hypothesis(property_vect const &hyp, int i): generator(hyp[i]), idx(i) {}
};

struct generator_assign: generator {
  virtual node *do_it() { gen->do_it(); /* TODO: theorem(assign) + modus */ return NULL; }
  generator *gen;
  generator_assign(generator *g, property const &r): generator(r), gen(g) {}
  ~generator_assign() { delete gen; }
};

struct generator_reflexive: generator {
  virtual node *do_it() { /* TODO */ return NULL; }
  static property_error generate(variable *v, int error) {
    property_error p;
    p.var = v;
    p.real = new ast_real(v);
    p.err = interval(interval_variant(interval_real()));
    p.error = error;
    return p;
  }
  generator_reflexive(variable *v, int e): generator(generate(v, e)) {}
};

struct generator_plouf: generator {
  virtual node *do_it() { return NULL; }
  generator_plouf(property const &p): generator(p) {}
};

/*
struct generator_plouf: generator {
  generator_plouf(node *) {}
  virtual node *do_it() { throw; }
};
*/

template< class T >
struct auto_deleter {
  mutable T *value;
  auto_deleter(): value(NULL) {}
  auto_deleter(T *v): value(v) {}
  auto_deleter(auto_deleter const &v) { value = v.value; v.value = NULL; }
  ~auto_deleter() { if (value) delete value; }
  T *release() { T *v = value; value = NULL; return v; }
  //T *operator T *() const { return value; }
  auto_deleter &operator =(T *v) { value = v; return *this; }
  auto_deleter &operator =(auto_deleter const &v) { value = v.value; v.value = NULL; return *this; }
  T &operator *() const { return *value; }
  T *operator ->() const { return value; }
  operator bool() const { return value; }
  bool operator !() const { return !value; }
};

}

struct do_generate_basic_proof: boost::static_visitor< generator * > {
  property_vect const &hyp;
  do_generate_basic_proof(property_vect const &h): hyp(h) {}
  generator *operator()(property_bound const &res) const;
  generator *operator()(property_error const &res) const;
};

generator *do_generate_basic_proof::operator()(property_bound const &res) const {
  //std::cout << resb->var->name->name << " in " << resb->bnd << std::endl;
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (inst.fun == NULL) {
    property_bound p = res;
    p.var = inst.in[0];
    generator *g = generate_basic_proof(hyp, p);
    if (!g) return NULL;
    property_bound *r = boost::get< property_bound >(&g->res);
    assert(r);
    p = *r;
    p.var = res.var;
    return new generator_assign(g, p);
  }
  int l = inst.in.size();
  std::vector< auto_deleter < generator > > gens;
  for(int i = 0; i < l; i++) {
    property_bound p;
    p.var = inst.in[i];
    generator *g = generate_basic_proof(hyp, p);
    if (!g) return NULL;
    gens.push_back(g);
  }
  assert(l == 2);
  property_bound *lhs = boost::get< property_bound >(&gens[0]->res);
  property_bound *rhs = boost::get< property_bound >(&gens[1]->res);
  assert(lhs && rhs);
  property_bound p = res;
  if (inst.fun->name->name == "add32") p.bnd = lhs->bnd + rhs->bnd;
  else if (inst.fun->name->name == "mul32") p.bnd = lhs->bnd * rhs->bnd;
  else assert(false);
  //if (!(p > res)) return NULL;
  return new generator_plouf(p);
}

generator *do_generate_basic_proof::operator()(property_error const &res) const {
  //static char const *type[] = { "ABS", "REL" };
  //std::cout << type[rese->error] << '(' << rese->var->name->name << ", " << *rese->real << ") in " << rese->err << std::endl;
  if (variable *const *v = boost::get< variable *const >(res.real))
    if (res.var == *v) return new generator_reflexive(res.var, res.error);
  int idx = res.var->get_definition();
  if (idx == -1) return NULL; /* TODO: unprovable? */
  instruction &inst = program[idx];
  if (inst.fun == NULL) {
    property_error p = res;
    p.var = inst.in[0];
    generator *g = generate_basic_proof(hyp, p);
    if (!g) return NULL;
    property_error *r = boost::get< property_error >(&g->res);
    assert(r);
    p = *r;
    p.var = res.var;
    return new generator_assign(g, p);
  }
  if (res.error != 0) return NULL;
  int l = inst.in.size();
  if (unary_op const *o = boost::get< unary_op const >(res.real)) {
    if (l != 1 || o->type != inst.fun->real_op) return NULL;
    /* TODO */
    return NULL;
  }
  if (binary_op const *o = boost::get< binary_op const >(res.real)) {
    if (l != 2 || o->type != inst.fun->real_op) return NULL;
    property_bound pb;
    property_error pe;
    pe.error = 0;
    if (inst.fun->name->name == "add32") {
      auto_deleter< generator > g_lhs, g_rhs, gb_res;
      pe.var = inst.in[0];
      pe.real = &o->left;
      g_lhs = generate_basic_proof(hyp, pe);
      if (!g_lhs) return NULL;
      property_error *p_lhs = boost::get< property_error >(&g_lhs->res);
      pe.var = inst.in[1];
      pe.real = &o->right;
      g_rhs = generate_basic_proof(hyp, pe);
      if (!g_rhs) return NULL;
      property_error *p_rhs = boost::get< property_error >(&g_rhs->res);
      pb.var = inst.out[0];
      if (!(gb_res = generate_basic_proof(hyp, pb))) return NULL;
      property_bound *pb_res = boost::get< property_bound >(&gb_res->res);
      assert(p_lhs && p_rhs && p_lhs->error == 0 && p_rhs->error == 0 && pb_res);
      property_error p = res;
      p.err = p_lhs->err + p_rhs->err + from_exponent(ulp_exponent(pb_res->bnd), GMP_RNDN);
      return new generator_plouf(p);
    }
    if (inst.fun->name->name == "mul32") {
      auto_deleter< generator > gb_lhs, gb_rhs, gb_res, ge_lhs, ge_rhs;
      pe.var = inst.in[0];
      pe.real = &o->left;
      if (!(ge_lhs = generate_basic_proof(hyp, pe))) return NULL;
      property_error *pe_lhs = boost::get< property_error >(&ge_lhs->res);
      pe.var = inst.in[1];
      pe.real = &o->right;
      if (!(ge_rhs = generate_basic_proof(hyp, pe))) return NULL;
      property_error *pe_rhs = boost::get< property_error >(&ge_rhs->res);
      pb.var = inst.in[0];
      if (!(gb_lhs = generate_basic_proof(hyp, pb))) return NULL;
      property_bound *pb_lhs = boost::get< property_bound >(&gb_lhs->res);
      pb.var = inst.in[1];
      if (!(gb_rhs = generate_basic_proof(hyp, pb))) return NULL;
      property_bound *pb_rhs = boost::get< property_bound >(&gb_rhs->res);
      pb.var = inst.out[0];
      if (!(gb_res = generate_basic_proof(hyp, pb))) return NULL;
      property_bound *pb_res = boost::get< property_bound >(&gb_res->res);
      assert(pe_lhs && pe_rhs && pe_lhs->error == 0 && pe_rhs->error == 0 && pb_lhs && pb_rhs && pb_res);
      property_error p = res;
      p.err = pe_lhs->err * to_real(pb_rhs->bnd) + pe_rhs->err * to_real(pb_lhs->bnd)
            + pe_lhs->err * pe_rhs->err + from_exponent(ulp_exponent(pb_res->bnd), GMP_RNDN);
      return new generator_plouf(p);
    }
  }
  assert(false);
  return NULL;
}

generator *generate_basic_proof(property_vect const &hyp, property const &res) {
  /*if (node *n = graph.find_compatible_node(hyp, res)) {
    return new generator_plouf(n);*/
  int i = hyp.find_compatible_property(res);
  if (i >= 0) return new generator_hypothesis(hyp, i);
  return boost::apply_visitor(do_generate_basic_proof(hyp), res);
}
