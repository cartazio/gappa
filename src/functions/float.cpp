#include "../ast.hpp"
#include "../program.hpp"
#include "../function.hpp"
#include "../interval.hpp"
#include "../property.hpp"
#include "../proof_graph.hpp"
#include <boost/preprocessor/cat.hpp>
#include <boost/preprocessor/stringize.hpp>

static type_id args32[3] = { FLOAT32, FLOAT32, UNDEFINED };
static type_id args64[3] = { FLOAT64, FLOAT64, UNDEFINED };
static type_id args80[3] = { FLOAT80, FLOAT80, UNDEFINED };
static type_id args128[3] = { FLOAT128, FLOAT128, UNDEFINED };
static type_id ret32[2] = { FLOAT32, UNDEFINED };
static type_id ret64[2] = { FLOAT64, UNDEFINED };
static type_id ret80[2] = { FLOAT80, UNDEFINED };
static type_id ret128[2] = { FLOAT128, UNDEFINED };

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

#define bop_definition(type, TYPE, PREC)	\
  fun = new function(BOP_##TYPE);		\
  fun->args_type = args##PREC;			\
  fun->return_type = ret##PREC;				\
  fun->matches = match;				\
  ast_ident::find(BOOST_PP_STRINGIZE(BOOST_PP_CAT(type, PREC)))->fun = fun

#define bop_definitions(type, TYPE)	\
  function *fun;			\
  bop_definition(type, TYPE, 32);	\
  bop_definition(type, TYPE, 64);	\
  bop_definition(type, TYPE, 80);	\
  bop_definition(type, TYPE, 128);

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

void initialize_add() {
  static function_match match[3] = {
    { { -1, HYP_BND }, const_add_float_bnd, &compute_add_float_bnd, { generate_bound: &generate_add_float_bnd } },
    { { -1, HYP_ABS }, const_add_float_abs, &compute_add_float_abs, { generate_error: &generate_add_float_abs } },
    { { 0 } } };
  bop_definitions(add, ADD);
}

/********** sub **********/

static hypothesis_constraint const_sub_float_bnd[3] = { { 1, HYP_BND }, { 2, HYP_BND }, { 0 } };

static interval compute_sub_float_bnd(interval const **ints) {
  return *ints[0] - *ints[1];
}

static node *generate_sub_float_bnd(property_vect const &hyp, property_bound &res) {
  interval const *ints[2];
  extract_intervals(hyp, ints);
  res.bnd = compute_sub_float_bnd(ints);
  return new node_theorem(hyp, res, "sub");
}

static hypothesis_constraint const_sub_float_abs[4] = { { -1, HYP_BND }, { 1, HYP_ABS }, { 2, HYP_ABS }, { 0 } };

static interval compute_sub_float_abs(interval const **ints) {
  return *ints[1] + *ints[2] + from_exponent(ulp_exponent(*ints[0]), GMP_RNDN);
}

static node *generate_sub_float_abs(property_vect const &hyp, property_error &res) {
  interval const *ints[3];
  extract_intervals(hyp, ints);
  res.err = compute_sub_float_abs(ints);
  return new node_theorem(hyp, res, "sub");
}

void initialize_sub() {
  static function_match match[3] = {
    { { -1, HYP_BND }, const_sub_float_bnd, &compute_sub_float_bnd, { generate_bound: &generate_sub_float_bnd } },
    { { -1, HYP_ABS }, const_sub_float_abs, &compute_sub_float_abs, { generate_error: &generate_sub_float_abs } },
    { { 0 } } };
  bop_definitions(sub, SUB);
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

void initialize_mul() {
  static function_match match[3] = {
    { { -1, HYP_BND }, const_mul_float_bnd, &compute_mul_float_bnd, { generate_bound: &generate_mul_float_bnd } },
    { { -1, HYP_ABS }, const_mul_float_abs, &compute_mul_float_abs, { generate_error: &generate_mul_float_abs } },
    { { 0 } } };
  bop_definitions(mul, MUL);
}
