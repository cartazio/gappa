#ifndef PROOFS_PROOF_GRAPH_HPP
#define PROOFS_PROOF_GRAPH_HPP

#include "proofs/property.hpp"
#include <map>
#include <set>
#include <vector>

enum node_id { HYPOTHESIS, AXIOM, THEOREM, MODUS, UNION, INTERSECTION, GRAPH };

struct node;
struct graph_t;

extern graph_t *top_graph;

typedef std::vector< node * > node_vect;
typedef std::set< node * > node_set;
typedef std::map< ast_real const *, node * > node_map;

struct node {
  node_id type;
  node_set succ;
  graph_t *graph;
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

class result_node: public node {
  property res;
 protected:
  property_vect hyp;
  result_node(node_id, property const &, graph_t * = top_graph);
 public:
  virtual property const &get_result() const { return res; }
  virtual property_vect const &get_hypotheses() const { return hyp; }
};

struct axiom_node: public result_node {
  axiom_node(property_vect const &h, property const &p): result_node(AXIOM, p, NULL) { hyp = h; }
};

struct theorem_node: public result_node {
  std::string name;
  theorem_node(int nb, property const h[], property const &p, std::string const &n);
  virtual ast_real_vect sub_expressions() const { return ast_real_vect(); }
};

class dependent_node: public result_node {
  node_vect pred;
 protected:
  dependent_node(node_id t, property const &p): result_node(t, p) {}
  void insert_pred(node *n);
 public:
  virtual node_vect const &get_subproofs() const { return pred; }
  virtual void clean_dependencies();
  virtual dependent_node::~dependent_node();
};

struct modus_node: public dependent_node {
  modus_node(int nb, node *nodes[], node *n);
};

struct proof_helper;

class graph_node;

class graph_t {
  graph_t *father;
  graph_node *known_node;
  node_set nodes;		// nodes owned by the graph, each node is implied by hyp
  node_set axioms;		// unusuable axioms (not implied by hyp)
  node_map known_reals;		// best node implied by hyp for each real
  property_vect hyp;		// hypotheses of the graph (they imply the hypotheses from the super-graph)
  property_vect goals;		// goals of the graph (they keep nodes alive)
  bool owned_helper;
 public:
  proof_helper *helper;
  void insert(node *n) { nodes.insert(n); }
  void remove(node *n) { nodes.erase (n); }
  void insert_axiom(node *);
  void remove_axiom(node *n) { axioms.erase(n); }
  graph_t(graph_t *, property_vect const &, property_vect const &, proof_helper *, bool);
  ~graph_t();
  node *find_already_known(ast_real const *) const;
  node_vect find_useful_axioms(ast_real const *);
  bool try_real(node *);
  property_vect const &get_hypotheses() const { return hyp; }
  property_vect const &get_goals() const { return goals; }
  ast_real_vect get_known_reals() const;
  bool dominates(graph_t const *) const;
  void populate();		// fill the proof graph
  void purge(node * = NULL);	// remove all the unused nodes, except for this one
  void flatten();		// move all the nodes in the upper graph
  void migrate();		// move all the free nodes in the upper graph
};

struct graph_loader {
  graph_t *old_graph;
  graph_loader(graph_t *g): old_graph(top_graph) { top_graph = g; }
  ~graph_loader() { top_graph = old_graph; }
};

#endif // PROOFS_PROOF_GRAPH_HPP
