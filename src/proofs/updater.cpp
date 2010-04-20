/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "proofs/updater.hpp"

/**
 * Returns @a opt if it is bounded, a mix with @a cur otherwise.
 * @pre @a cur is a bounded subset of @a opt.
 */
property boundify(property const &opt, property const &cur)
{
  property res = opt;
  interval const &bopt = opt.bnd(), &bcur = cur.bnd();
  if (is_bounded(bopt)) return res;
  res.bnd() = (lower(bopt) == number::neg_inf) ?
    interval(lower(bcur), upper(bopt)) :
    interval(lower(bopt), upper(bcur));
  return res;
}

/**
 * Returns a fully simplified mix of @a opt with @a cur.
 * Ensures the bounds do not cross the points -1, 0, and -1.
 * @pre @a cur is a bounded subset of @a opt.
 * @see ::simplify_full
 */
static property boundify_full(property const &opt, property const &cur)
{
  property res = opt;
  interval const &bopt = opt.bnd(), &bcur = cur.bnd();
  if (is_bounded(bopt)) return res;
  res.bnd() = (lower(bopt) == number::neg_inf) ?
    interval(simplify_full(lower(bcur), -1), upper(bopt)) :
    interval(lower(bopt), simplify_full(upper(bcur), 1));
  return res;
}

struct trivial_updater1: theorem_updater
{
  virtual void expand(theorem_node *n, property const &p)
  { n->res = boundify_full(p, n->res); }
};
static trivial_updater1 trivial_updater2;
/** Updater for setting the result to the passed argument. */
theorem_updater *trivial_updater = &trivial_updater2; 

struct identity_updater1: theorem_updater
{
  virtual void expand(theorem_node *n, property const &p)
  {
    n->res = boundify_full(p, n->res);
    unsigned sz = n->hyp.size();
    if (sz > 0) n->hyp[sz - 1].bnd() = n->res.bnd();
  }
};
static identity_updater1 identity_updater2;
/** Updater for setting the result and the last hypothesis to the passed argument. */
theorem_updater *identity_updater = &identity_updater2;

void unary_interval_updater::expand(theorem_node *n, property const &p)
{
  int b = 3;
  property res = p;
  interval const &bnd = p.bnd();
  interval &ih = n->hyp[0].bnd(), &ir = res.bnd();
  interval hyp = ih;
  while (b != 0) {
    if (b & 1) {
      number const &old = lower(ih);
      number m = simplify(old, -1);
      if (m != old) {
        hyp = interval(m, upper(ih));
        (*compute)(hyp, ir);
        if (!(ir <= bnd)) { hyp = ih; b &= ~1; }
        else ih = hyp;
      } else b &= ~1;
    }
    if (b & 2) {
      number const &old = upper(ih);
      number m = simplify(old, 1);
      if (m != old) {
        hyp = interval(lower(ih), m);
        (*compute)(hyp, ir);
        if (!(ir <= bnd)) { hyp = ih; b &= ~2; }
        else ih = hyp;
      } else b &= ~2;
    }
  }
  (*compute)(hyp, ir);
  n->res = boundify(p, res);
}

void binary_interval_updater::expand(theorem_node *n, property const &p)
{
  int b = 15;
  property res = p;
  interval const &bnd = p.bnd();
  interval &i1 = n->hyp[0].bnd(), &i2 = n->hyp[1].bnd(), &ir = res.bnd();
  interval hyps[] = { i1, i2 };
  while (b != 0) {
    if (b & 1) {
      number const &old = lower(i1);
      number m = simplify(old, -1);
      if (m != old) {
        hyps[0] = interval(m, upper(i1));
        (*compute)(hyps, ir);
        if (!(ir <= bnd)) { hyps[0] = i1; b &= ~1; }
        else i1 = hyps[0];
      } else b &= ~1;
    }
    if (b & 2) {
      number const &old = upper(i1);
      number m = simplify(old, 1);
      if (m != old) {
        hyps[0] = interval(lower(i1), m);
        (*compute)(hyps, ir);
        if (!(ir <= bnd)) { hyps[0] = i1; b &= ~2; }
        else i1 = hyps[0];
      } else b &= ~2;
    }
    if (b & 4) {
      number const &old = lower(i2);
      number m = simplify(old, -1);
      if (m != old) {
        hyps[1] = interval(m, upper(i2));
        (*compute)(hyps, ir);
        if (!(ir <= bnd)) { hyps[1] = i2; b &= ~4; }
        else i2 = hyps[1];
      } else b &= ~4;
    }
    if (b & 8) {
      number const &old = upper(i2);
      number m = simplify(old, 1);
      if (m != old) {
        hyps[1] = interval(lower(i2), m);
        (*compute)(hyps, ir);
        if (!(ir <= bnd)) { hyps[1] = i2; b &= ~8; }
        else i2 = hyps[1];
      } else b &= ~8;
    }
  }
  (*compute)(hyps, ir);
  n->res = boundify(p, res);
}
