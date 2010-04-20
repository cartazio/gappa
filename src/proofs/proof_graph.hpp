/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#ifndef PROOFS_PROOF_GRAPH_HPP
#define PROOFS_PROOF_GRAPH_HPP

#include <map>
#include <set>
#include <vector>
#include "proofs/dichotomy.hpp"
#include "proofs/property.hpp"

/** Category of a node in a proof graph. */
enum node_id
{
  HYPOTHESIS,   /**< A property found on the left hand side of an implication. */
  MODUS,        /**< The application of a theorem of the database. */
  UNION,        /**< The parent node of all the related nodes of a dichotomy. */
  INTERSECTION, /**< The intersection between two nodes on the same real. */
  GOAL          /**< A property found on the right hand side of an application. */
};

struct node;
struct graph_t;

/** Current graph, to which new nodes are added. */
extern graph_t *top_graph;

struct theorem_updater;

/** Specific instanciation of a theorem. */
struct theorem_node
{
  property res;             /**< Proven result. */
  property_vect hyp;        /**< Properties needed as hypotheses for proving the result. */
  std::string name;         /**< Unmangled name of the theorem. */
  theorem_updater *updater; /**< Function for simplifying the hypotheses in case the goal can be weakened. */
  theorem_node(int, property const [], property const &, std::string const &, theorem_updater *);
};

struct theorem_updater
{
  virtual void expand(theorem_node *, property const &) = 0;
  virtual ~theorem_updater() {}
};

typedef std::vector< node * > node_vect;
typedef std::set< node * > node_set;
typedef std::map< predicated_real, node * > node_map;

/**
 * Node of a proof graph.
 * @invariant Pointers to a node are stored:
 * \li in dependent_node::pred, these nodes are referenced by #succ,
 * \li in graph_t::known_reals and graph_t::contradiction, these pointers are counted by #nb_good.
 */
struct node
{
  node_id type;             /**< Type of this node. */
  node_set succ;            /**< All the nodes that immediatly depend on this node. */
  graph_t *graph;           /**< The graph owning this node, if any. */
  unsigned nb_good;         /**< Number of references by all the graph_t::known_reals. */
  unsigned nb_missing;      /**< Heuristic number of missing facts in unconstrained mode. */
  mutable unsigned visited; /**< Timestamp of the last visit by an algorithm. */
  unsigned local_weight;    /**< Local weight of the node, usually 1. */
  unsigned weight;          /**< Total weight of all the ancestors, computed on demand. */
  bool can_visit() const;
  unsigned get_weight();
  node(node_id, graph_t *);
  /** Returns the property this node proves. */
  virtual property const &get_result() const = 0;
  virtual node_vect const &get_subproofs() const;
  virtual ~node();
  void remove_known();
  void remove_succ(node const *);
  virtual property maximal() const;
  /** Returns the widest result that node @a n (an immediate ancestor of this node) can prove without changing the result proved by this node. */
  virtual property maximal_for(node const *n) const = 0;
  virtual void enlarge(property const &) = 0;
};

/** Node of type ::HYPOTHESIS. */
class hypothesis_node: public node
{
  property const &res; /**< Reference to an hypothesis of the parent graph. */
 public:
  hypothesis_node(property const &p): node(HYPOTHESIS, top_graph), res(p) {}
  virtual property const &get_result() const { return res; }
  virtual property maximal() const { return res; }
  virtual property maximal_for(node const *) const { assert(false); }
  virtual void enlarge(property const &) { assert(false); }
};

/** Node refering to other nodes previously proven. */
class dependent_node: public node
{
  node_vect pred;
 protected:
  dependent_node(node_id t,  graph_t *g = top_graph): node(t, g) {}
  void insert_pred(node *n);
  void clean_dependencies();
 public:
  virtual node_vect const &get_subproofs() const { return pred; }
  virtual ~dependent_node() { clean_dependencies(); }
};

node *create_theorem(int, property const [], property const &, std::string const &, theorem_updater * = NULL);

/** Node of type ::MODUS */
class modus_node: public dependent_node
{
 public:
  theorem_node *target;
  modus_node(theorem_node *);
  /** Returns the result stored in #target. */
  virtual property const &get_result() const { return target->res; }
  virtual ~modus_node();
  virtual property maximal_for(node const *) const;
  virtual void enlarge(property const &);
};

/**
 * Graph of nodes.
 * @invariant All the nodes from #nodes are (indirectly accessible from nodes) stored in #known_reals, #partial_reals, and #contradiction.
 *            This property is temporarily false between node construction and #try_real.
 * @invariant If #contradiction is set, #known_reals and #partial_reals are empty.
 */
class graph_t
{
  graph_t *father;        /**< Parent graph. */
  node_set nodes;         /**< Nodes owned by this graph. Each node can be proved in the context of #hyp. */
  node_map known_reals;   /**< Best node implied by #hyp for each real. */
  node_map partial_reals; /**< Partly-bounded hypotheses that have yet to be used by an intersection_node. */
  property_vect hyp;      /**< Hypotheses of this graph. They imply the hypotheses of the #father graph. */
  node *contradiction;    /**< Node proving an empty result, thus proving anything. */
 public:
  /** Inserts a node in the graph. */
  void insert(node *n) { nodes.insert(n); }
  /** Removes a node from the graph. */
  void remove(node *n) { nodes.erase (n); }
  graph_t(graph_t *, property_vect const &);
  ~graph_t();
  node *find_already_known(predicated_real const &) const;
  bool try_real(node *&);
  /** Returns the hypotheses #hyp of this graph. */
  property_vect const &get_hypotheses() const { return hyp; }
  bool dominates(graph_t const *) const;
  void populate(property_tree const &, property_tree const &,
    dichotomy_sequence const &, int);
  void dichotomize(property_tree const &, dichotomy_hint const &, int);
  /** Returns the #contradiction node of this graph, if any. */
  node *get_contradiction() const { return contradiction; }
  void purge();
  void set_contradiction(node *);
  void replace_known(node_vect const &);
  void show_dangling() const;
};

/** Helper for keeping ::top_graph up-to-date. */
struct graph_loader
{
  graph_t *old_graph;
  /** Sets @a g as the new ::top_graph. */
  graph_loader(graph_t *g): old_graph(top_graph) { top_graph = g; }
  /** Restores the previously set ::top_graph. */
  ~graph_loader() { top_graph = old_graph; }
};

void enlarger(node_vect const &);

#endif // PROOFS_PROOF_GRAPH_HPP
