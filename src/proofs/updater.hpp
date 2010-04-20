/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PROOFS_UPDATER_HPP
#define PROOFS_UPDATER_HPP

#include "proofs/proof_graph.hpp"

extern theorem_updater *trivial_updater, *identity_updater;

property boundify(property const &opt, property const &cur);

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
