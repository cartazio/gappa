#include "../ast.hpp"
#include "../program.hpp"
#include "../function.hpp"
#include "../interval.hpp"
#include "../property.hpp"
#include "../proof_graph.hpp"

static type_id args[3] = { FLOAT32, FLOAT32, UNDEFINED };
static type_id ret[2] = { FLOAT32, UNDEFINED };

struct node_theorem: node {
  std::string name;
  node_theorem(property_vect const &h, property const &p, std::string const &n): node(THEOREM) {
    res = p;
    hyp = h;
    name = n;
  }
};

static void extract_intervals(property_vect const &hyp, interval const **ints) {
  for(int i = 0, l = hyp.size(); i < l; ++i) {
    if (property_bound const *p = boost::get< property_bound const >(&hyp[i])) ints[i] = &p->bnd; else
    if (property_error const *p = boost::get< property_error const >(&hyp[i])) ints[i] = &p->err; else
    assert(false);
  }
}

/********** add **********/

static hypothesis_constraint const_add_float_bnd[3] = { { 1, HYP_BND }, { 2, HYP_BND }, { 0 } };

static interval compute_add_float_bnd(interval const **ints) {
  return *ints[0] + *ints[1];
}

static node *generate_add_float_bnd(property_vect const &hyp, property_bound &res) {
  interval const *ints[2];
  extract_intervals(hyp, ints);
  res.bnd = compute_add_float_bnd(ints);
  return new node_theorem(hyp, res, "add");
}

static hypothesis_constraint const_add_float_abs[4] = { { -1, HYP_BND }, { 1, HYP_ABS }, { 2, HYP_ABS }, { 0 } };

static interval compute_add_float_abs(interval const **ints) {
  return *ints[1] + *ints[2] + from_exponent(ulp_exponent(*ints[0]), GMP_RNDN);
}

static node *generate_add_float_abs(property_vect const &hyp, property_error &res) {
  interval const *ints[3];
  extract_intervals(hyp, ints);
  res.err = compute_add_float_abs(ints);
  return new node_theorem(hyp, res, "add");
}

void initialize_add32() {
  ast_ident *id = ast_ident::find("add32");
  id->fun = new function(id, BOP_ADD);
  id->fun->return_type = ret;
  id->fun->args_type = args;
  static function_match match[3] = {
    { { -1, HYP_BND }, const_add_float_bnd, &compute_add_float_bnd, { generate_bound: &generate_add_float_bnd } },
    { { -1, HYP_ABS }, const_add_float_abs, &compute_add_float_abs, { generate_error: &generate_add_float_abs } },
    { { 0 } } };
  id->fun->matches = match;
}

/********** mul **********/

static hypothesis_constraint const_mul_float_bnd[3] = { { 1, HYP_BND }, { 2, HYP_BND }, { 0 } };

static interval compute_mul_float_bnd(interval const **ints) {
  return *ints[0] * *ints[1];
}

static node *generate_mul_float_bnd(property_vect const &hyp, property_bound &res) {
  interval const *ints[2];
  extract_intervals(hyp, ints);
  res.bnd = compute_mul_float_bnd(ints);
  return new node_theorem(hyp, res, "mul");
}

static hypothesis_constraint const_mul_float_abs[6] =
  { { -1, HYP_BND }, { 1, HYP_BND }, { 2, HYP_BND }, { 1, HYP_ABS }, { 2, HYP_ABS }, { 0 } };

static interval compute_mul_float_abs(interval const **ints) {
  return *ints[3] * to_real(*ints[2]) + *ints[4] * to_real(*ints[1]) + from_exponent(ulp_exponent(*ints[0]), GMP_RNDN);
}

static node *generate_mul_float_abs(property_vect const &hyp, property_error &res) {
  interval const *ints[5];
  extract_intervals(hyp, ints);
  res.err = compute_mul_float_abs(ints);
  return new node_theorem(hyp, res, "mul");
}

void initialize_mul32() {
  ast_ident *id = ast_ident::find("mul32");
  id->fun = new function(id, BOP_MUL);
  id->fun->return_type = ret;
  id->fun->args_type = args;
  static function_match match[3] = {
    { { -1, HYP_BND }, const_mul_float_bnd, &compute_mul_float_bnd, { generate_bound: &generate_mul_float_bnd } },
    { { -1, HYP_ABS }, const_mul_float_abs, &compute_mul_float_abs, { generate_error: &generate_mul_float_abs } },
    { { 0 } } };
  id->fun->matches = match;
}
