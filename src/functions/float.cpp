#include "ast.hpp"
#include "program.hpp"
#include "function.hpp"
#include "numbers/real.hpp"
#include "numbers/float.hpp"
#include "numbers/interval_ext.hpp"
#include "property.hpp"
#include "proof_graph.hpp"
#include <boost/preprocessor/cat.hpp>
#include <boost/preprocessor/stringize.hpp>

int ulp_exponent(interval const &);
int mig_exponent(interval const &);
int mag_exponent(interval const &);
interval from_exponent(int, int);

static type_id args32_b[3] = { interval_float32, interval_float32, 0 };
static type_id args64_b[3] = { interval_float64, interval_float64, 0 };
static type_id args80_b[3] = { interval_floatx80, interval_floatx80, 0 };
static type_id args128_b[3] = { interval_float128, interval_float128, 0 };
static type_id ret32[2] = { interval_float32, 0 };
static type_id ret64[2] = { interval_float64, 0 };
static type_id ret80[2] = { interval_floatx80, 0 };
static type_id ret128[2] = { interval_float128, 0 };

struct node_theorem: node {
  char const *name;
  node_theorem(int nb, property const *h, property const &p, char const *n): node(THEOREM), name(n) {
    res = p;
    for(int i = 0; i < nb; ++i) hyp.push_back(h[i]);
  }
};

#define bop_definition(type, TYPE, PREC)	\
  fun = new function(BOP_##TYPE);		\
  fun->args_type = args##PREC##_b;		\
  fun->return_type = ret##PREC;			\
  fun->bnd_comp = &bnd_comp;			\
  fun->err_comp = err_comp;			\
  ast_ident::find(BOOST_PP_STRINGIZE(BOOST_PP_CAT(type, PREC)))->fun = fun

#define bop_definitions(type, TYPE)	\
  static bound_computation const bnd_comp = { bound_compute_##type##_float, bound_generate_##type##_float };	\
  function *fun;			\
  bop_definition(type, TYPE, 32);	\
  bop_definition(type, TYPE, 64);	\
  bop_definition(type, TYPE, 80);	\
  bop_definition(type, TYPE, 128);

#define do_constraint(TYPE, name)	\
  { { -1, HYP_##TYPE }, const_##name, &compute_##name, &generate_##name }

static interval const one = interval(interval_real, new _interval_real(number_real(1)));

/********** add **********/

static interval bound_compute_add_float(interval const **ints) {
  return *ints[0] + *ints[1];
}

static node *bound_generate_add_float(property const *hyp, property const &res) {
  return new node_theorem(2, hyp, res, "add");
}

static hypothesis_constraint const const_add_float_abs[4] =
  { { 1, HYP_ABS }, { 2, HYP_ABS }, { -1, HYP_BND }, { 0 } };

static interval compute_add_float_abs(interval const **ints) {
  return *ints[0] + *ints[1] + from_exponent(ulp_exponent(*ints[2]), 0);
}

static node *generate_add_float_abs(property const *hyp, property const &res) {
  return new node_theorem(3, hyp, res, "add");
}

static hypothesis_constraint const const_add_float_abs_sterbenz[6] =
  { { 1, HYP_BND }, { 2, HYP_BND }, { 1, HYP_ABS }, { 2, HYP_ABS }, { -1, HYP_BND }, { 0 } };

static interval compute_add_float_abs_sterbenz(interval const **ints) {
  int e = mag_exponent(*ints[4]);
  if (e > mig_exponent(*ints[0]) || e > mig_exponent(*ints[1])) return interval();
  return *ints[2] + *ints[3];
}

static node *generate_add_float_abs_sterbenz(property const *hyp, property const &res) {
  return new node_theorem(5, hyp, res, "add_sterbenz");
}

static hypothesis_constraint const const_add_float_abs_singleton[5] =
  { { 1, HYP_SNG }, { 2, HYP_SNG }, { 1, HYP_ABS }, { 2, HYP_ABS }, { 0 } };

static interval compute_add_float_abs_singleton(interval const **ints) {
  return to_real(*ints[0]) + to_real(*ints[1]) - to_real(*ints[0] + *ints[1]) + *ints[2] + *ints[3];
}

static node *generate_add_float_abs_singleton(property const *hyp, property const &res) {
  return new node_theorem(4, hyp, res, "add_singleton");
}

void initialize_add() {
  static const error_computation err_comp[4] = {
    do_constraint(ABS, add_float_abs_singleton),
    do_constraint(ABS, add_float_abs_sterbenz),
    do_constraint(ABS, add_float_abs),
    { { 0 } } };
  bop_definitions(add, ADD);
}

/********** sub **********/

static interval bound_compute_sub_float(interval const **ints) {
  return *ints[0] - *ints[1];
}

static node *bound_generate_sub_float(property const *hyp, property const &res) {
  return new node_theorem(2, hyp, res, "sub");
}

static hypothesis_constraint const const_sub_float_abs[4] =
  { { 1, HYP_ABS }, { 2, HYP_ABS }, { -1, HYP_BND }, { 0 } };

static interval compute_sub_float_abs(interval const **ints) {
  return *ints[0] - *ints[1] + from_exponent(ulp_exponent(*ints[2]), 0);
}

static node *generate_sub_float_abs(property const *hyp, property const &res) {
  return new node_theorem(3, hyp, res, "sub");
}

static hypothesis_constraint const const_sub_float_abs_sterbenz[6] =
  { { 1, HYP_BND }, { 2, HYP_BND }, { 1, HYP_ABS }, { 2, HYP_ABS }, { -1, HYP_BND }, { 0 } };

static interval compute_sub_float_abs_sterbenz(interval const **ints) {
  int e = mag_exponent(*ints[4]);
  if (e > mig_exponent(*ints[0]) || e > mig_exponent(*ints[1])) return interval();
  return *ints[2] - *ints[3];
}

static node *generate_sub_float_abs_sterbenz(property const *hyp, property const &res) {
  return new node_theorem(5, hyp, res, "sub_sterbenz");
}

static hypothesis_constraint const const_sub_float_abs_singleton[5] =
  { { 1, HYP_SNG }, { 2, HYP_SNG }, { 1, HYP_ABS }, { 2, HYP_ABS }, { 0 } };

static interval compute_sub_float_abs_singleton(interval const **ints) {
  return to_real(*ints[0]) - to_real(*ints[1]) - to_real(*ints[0] - *ints[1]) + *ints[2] - *ints[3];
}

static node *generate_sub_float_abs_singleton(property const *hyp, property const &res) {
  return new node_theorem(4, hyp, res, "sub_singleton");
}

void initialize_sub() {
  static const error_computation err_comp[4] = {
    do_constraint(ABS, sub_float_abs_singleton),
    do_constraint(ABS, sub_float_abs_sterbenz),
    do_constraint(ABS, sub_float_abs),
    { { 0 } } };
  bop_definitions(sub, SUB);
}

/********** mul **********/

static interval bound_compute_mul_float(interval const **ints) {
  return *ints[0] * *ints[1];
}

static node *bound_generate_mul_float(property const *hyp, property const &res) {
  return new node_theorem(2, hyp, res, "mul");
}

static hypothesis_constraint const const_mul_float_abs[6] =
  { { 1, HYP_BND }, { 2, HYP_BND }, { 1, HYP_ABS }, { 2, HYP_ABS }, { -1, HYP_BND }, { 0 } };

static interval compute_mul_float_abs(interval const **ints) {
  return *ints[2] * to_real(*ints[1]) + *ints[3] * to_real(*ints[0])
       + *ints[2] * *ints[3] + from_exponent(ulp_exponent(*ints[4]), 0);
}

static node *generate_mul_float_abs(property const *hyp, property const &res) {
  return new node_theorem(5, hyp, res, "mul");
}

static hypothesis_constraint const const_mul_float_abs_singleton[5] =
  { { 1, HYP_SNG }, { 2, HYP_SNG }, { 1, HYP_ABS }, { 2, HYP_ABS }, { 0 } };

static interval compute_mul_float_abs_singleton(interval const **ints) {
  interval i0 = to_real(*ints[0]), i1 = to_real(*ints[1]);
  return i0 * i1 - to_real(*ints[0] * *ints[1]) + *ints[2] * i1 + *ints[3] * i0 + *ints[2] * *ints[3];
}

static node *generate_mul_float_abs_singleton(property const *hyp, property const &res) {
  return new node_theorem(4, hyp, res, "mul_singleton");
}

static hypothesis_constraint const const_mul_float_rel[3] =
  { { 1, HYP_REL }, { 2, HYP_REL }, { 0 } };

static interval compute_mul_float_rel(interval const **ints) {
  return (one + *ints[0]) * (one + *ints[1]) * (one + from_exponent(-23, 0)) - one; // TODO
}

static node *generate_mul_float_rel(property const *hyp, property const &res) {
  return new node_theorem(2, hyp, res, "mul");
}

void initialize_mul() {
  static const error_computation err_comp[4] = {
    do_constraint(ABS, mul_float_abs_singleton),
    do_constraint(ABS, mul_float_abs),
    do_constraint(REL, mul_float_rel),
    { { 0 } } };
  bop_definitions(mul, MUL);
}

/********** init **********/

namespace  {

struct loader {
  loader();
};

loader::loader() {
  initialize_add();
  initialize_sub();
  initialize_mul();
}

loader init;

}
