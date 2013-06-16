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
#include "proofs/schemes.hpp"
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

void expand(theorem_node *n, property const &p)
{
  if (!n->sch) return;
  switch (n->sch->update_kind) {
  case UPD_TRIV:
    if (!n->res.real.pred_bnd()) return;
    n->res = boundify_full(p, n->res);
    return;
  case UPD_COPY: {
    if (!n->res.real.pred_bnd()) return;
    n->res = boundify_full(p, n->res);
    unsigned sz = n->hyp.size();
    if (sz > 0) n->hyp[sz - 1].bnd() = n->res.bnd();
    return; }
  case UPD_SEEK:
    break;
  default:
    assert(false);
  }
  unsigned b = ~0u;
  property *hyps = &n->hyp[0];
  int l = n->hyp.size();
  if (l > 16) l = 16;
  bool keep_going;
  do
  {
    keep_going = false;
    for (int i = 0; i != l; ++i)
    {
      if (!n->hyp[i].real.pred_bnd()) continue;
      interval &ih = n->hyp[i].bnd();
      interval old_ih = ih;
      unsigned mask = 1u << (2 * i);
      if (b & mask)
      {
        number const &old = lower(ih);
        number m = simplify(old, -1);
        if (m != old) {
          ih = interval(m, upper(ih));
          property res(n->sch->real);
          n->sch->compute(hyps, res, n->name);
          if (res.null() || !res.implies(n->res)) { ih = old_ih; b &= ~mask; }
          else { n->res = res; keep_going = true; old_ih = ih; }
        } else b &= ~mask;
      }
      mask = 1u << (2 * i + 1);
      if (b & mask)
      {
        number const &old = upper(ih);
        number m = simplify(old, 1);
        if (m != old) {
          ih = interval(lower(ih), m);
          property res(n->sch->real);
          n->sch->compute(hyps, res, n->name);
          if (res.null() || !res.implies(n->res)) { ih = old_ih; b &= ~mask; }
          else { n->res = res; keep_going = true; }
        } else b &= ~mask;
      }
    }
  } while (keep_going);
  if (n->res.real.pred_bnd()) n->res = boundify(p, n->res);
}
