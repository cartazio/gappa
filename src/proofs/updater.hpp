#ifndef PROOFS_UPDATER_HPP
#define PROOFS_UPDATER_HPP

#include "proofs/proof_graph.hpp"

struct unary_interval_updater: theorem_updater {
  typedef void (*fn)(interval const &, interval &);
  fn compute;
  unary_interval_updater(fn c): compute(c) {}
  virtual void expand(theorem_node *, property const &);
};

#define UNARY_INTERVAL(name) \
  static void name##_aux(interval const &, interval &); \
  static unary_interval_updater name(&name##_aux);       \
  static void name##_aux(interval const &h, interval &r)

struct binary_interval_updater: theorem_updater {
  typedef void (*fn)(interval const [], interval &);
  fn compute;
  binary_interval_updater(fn c): compute(c) {}
  virtual void expand(theorem_node *, property const &);
};

#define BINARY_INTERVAL(name) \
  static void name##_aux(interval const [], interval &); \
  static binary_interval_updater name(&name##_aux);       \
  static void name##_aux(interval const h[], interval &r)

#endif // PROOFS_UPDATER_HPP
