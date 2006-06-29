#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"
#include "proofs/updater.hpp"


struct trivial_updater1: theorem_updater {
  virtual void expand(theorem_node *n, property const &p) { n->res = p; }
};
static trivial_updater1 trivial_updater2;
theorem_updater *trivial_updater = &trivial_updater2; 

struct identity_updater1: theorem_updater {
  virtual void expand(theorem_node *n, property const &p) { n->res = p; n->hyp[0] = p; }
};
static identity_updater1 identity_updater2;
theorem_updater *identity_updater = &identity_updater2;

void unary_interval_updater::expand(theorem_node *n, property const &p) {
  int b = 3;
  property res = p;
  interval &ih = n->hyp[0].bnd(), &ir = res.bnd();
  interval hyp = ih;
  while (b != 0) {
    if (b & 1) {
      number const &old = lower(ih);
      number m = old;
      simplify(m, -1);
      if (m != old) {
        hyp = interval(m, upper(ih));
        (*compute)(hyp, ir);
        if (!(ir <= p.bnd())) { hyp = ih; b &= ~1; }
        else ih = hyp;
      } else b &= ~1;
    }
    if (b & 2) {
      number const &old = upper(ih);
      number m = old;
      simplify(m, 1);
      if (m != old) {
        hyp = interval(lower(ih), m);
        (*compute)(hyp, ir);
        if (!(ir <= p.bnd())) { hyp = ih; b &= ~2; }
        else ih = hyp;
      } else b &= ~2;
    }
  }
  n->res = p;
}

void binary_interval_updater::expand(theorem_node *n, property const &p) {
  int b = 15;
  property res = p;
  interval &i1 = n->hyp[0].bnd(), &i2 = n->hyp[1].bnd(), &ir = res.bnd();
  interval hyps[] = { i1, i2 };
  while (b != 0) {
    if (b & 1) {
      number const &old = lower(i1);
      number m = old;
      simplify(m, -1);
      if (m != old) {
        hyps[0] = interval(m, upper(i1));
        (*compute)(hyps, ir);
        if (!(ir <= p.bnd())) { hyps[0] = i1; b &= ~1; }
        else i1 = hyps[0];
      } else b &= ~1;
    }
    if (b & 2) {
      number const &old = upper(i1);
      number m = old;
      simplify(m, 1);
      if (m != old) {
        hyps[0] = interval(lower(i1), m);
        (*compute)(hyps, ir);
        if (!(ir <= p.bnd())) { hyps[0] = i1; b &= ~2; }
        else i1 = hyps[0];
      } else b &= ~2;
    }
    if (b & 4) {
      number const &old = lower(i2);
      number m = old;
      simplify(m, -1);
      if (m != old) {
        hyps[0] = interval(m, upper(i2));
        (*compute)(hyps, ir);
        if (!(ir <= p.bnd())) { hyps[1] = i2; b &= ~4; }
        else i2 = hyps[1];
      } else b &= ~4;
    }
    if (b & 8) {
      number const &old = upper(i2);
      number m = old;
      simplify(m, 1);
      if (m != old) {
        hyps[1] = interval(lower(i2), m);
        (*compute)(hyps, ir);
        if (!(ir <= p.bnd())) { hyps[1] = i2; b &= ~8; }
        else i2 = hyps[1];
      } else b &= ~8;
    }
  }
  n->res = p;
}
