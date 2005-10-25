#ifndef PROOFS_PROOF_GRAPH_HPP
#define PROOFS_PROOF_GRAPH_HPP

#include <map>
#include <set>
#include <vector>
#include "proofs/property.hpp"

enum node_id { HYPOTHESIS, MODUS, UNION, INTERSECTION };

struct node;
struct graph_t;

extern graph_t *top_graph;

struct theorem_node {
  property res;
  property_vect hyp;
  std::string name;
  theorem_node(int, property const [], property const &, std::string const &);
};

typedef std::vector< node * > node_vect;
typedef std::vector< theorem_node * > axiom_vect;
typedef std::set< node * > node_set;
typedef std::set< theorem_node * > axiom_set;
typedef std::map< predicated_real, node * > node_map;

struct node {
  node_id type;
  node_set succ;
  graph_t *graph;
  unsigned nb_good;
  node(node_id, graph_t *);
  virtual property const &get_result() const = 0;
  virtual property_vect const &get_hypotheses() const;
  virtual node_vect const &get_subproofs() const;
  virtual void clean_dependencies() {}
  virtual ~node();
};

class hypothesis_node: public node {
  property const &res;
 public:
  hypothesis_node(property const &p): node(HYPOTHESIS, top_graph), res(p) {}
  virtual property const &get_result() const { return res; }
};

class dependent_node: public node {
  node_vect pred;
 protected:
  dependent_node(node_id t,  graph_t *g = top_graph): node(t, g) {}
  void insert_pred(node *n);
 public:
  virtual node_vect const &get_subproofs() const { return pred; }
  virtual void clean_dependencies();
  virtual ~dependent_node();
};

node *create_theorem(int nb, property const h[], property const &p, std::string const &n);

class modus_node: public dependent_node {
  property_vect hyp;
 public:
  theorem_node *target;
  modus_node(theorem_node *);
  virtual property_vect const &get_hypotheses() const { return hyp; }
  virtual property const &get_result() const { return target->res; }
  virtual ~modus_node();
};

struct proof_helper;

class graph_t {
  graph_t *father;
  node_set nodes;		// nodes owned by the graph, each node is implied by hyp
  node_map known_reals;		// best node implied by hyp for each real
  property_vect hyp;		// hypotheses of the graph (they imply the hypotheses from the super-graph)
  property_vect goals;		// goals of the graph (they keep nodes alive)
  bool owned_helper;
  node *contradiction;
  friend class intersection_node;
 public:
  proof_helper *helper;
  void insert(node *n) { nodes.insert(n); }
  void remove(node *n) { nodes.erase (n); }
  graph_t(graph_t *, property_vect const &, property_vect const &, proof_helper *, bool);
  ~graph_t();
  node *find_already_known(predicated_real const &) const;
  bool try_real(node *);
  property_vect const &get_hypotheses() const { return hyp; }
  property_vect const &get_goals() const { return goals; }
  ast_real_vect get_known_reals() const;
  bool dominates(graph_t const *) const;
  bool populate();		// fill the proof graph, return true in case of contradiction
  void purge(node * = NULL);	// remove all the unused nodes, except for this one
  void flatten();		// move all the nodes in the upper graph
  bool migrate();		// move the free nodes in the upper graph, return true if any
  node *get_contradiction() const { return contradiction; }
};

struct graph_loader {
  graph_t *old_graph;
  graph_loader(graph_t *g): old_graph(top_graph) { top_graph = g; }
  ~graph_loader() { top_graph = old_graph; }
};

#endif // PROOFS_PROOF_GRAPH_HPP
