#ifndef PROOFS_PROOF_GRAPH_HPP
#define PROOFS_PROOF_GRAPH_HPP

#include "proofs/property.hpp"
#include <map>
#include <set>
#include <vector>

enum node_id { HYPOTHESIS, AXIOM, THEOREM, MODUS, UNION, INTERSECTION };

struct node;
struct graph_t;

typedef std::vector< node * > node_vect;
typedef std::set< node * > node_set;
typedef std::map< ast_real const *, node * > node_map;

struct node {
  node_id type;
  node(node_id t): type(t) {}
  virtual property const &get_result() const = 0;
  virtual property_vect const &get_hypotheses() const;
  virtual node_vect const &get_subproofs() const;
  virtual ~node() {}
};

class hypothesis_node: public node {
  property const &res;
 public:
  hypothesis_node(property const &p): node(HYPOTHESIS), res(p) {}
  virtual property const &get_result() const { return res; }
};

class result_node: public node {
  property res;
 protected:
  property_vect hyp;
  result_node(node_id, property const &, bool = true);
 public:
  virtual property const &get_result() const { return res; }
  virtual property_vect const &get_hypotheses() const { return hyp; }
};

struct axiom_node: public result_node {
  axiom_node(property_vect const &h, property const &p): result_node(AXIOM, p, false) { hyp = h; }
};

struct theorem_node: public result_node {
  std::string name;
  theorem_node(int nb, property const h[], property const &p, std::string const &n);
};

class dependent_node: public result_node {
  node_vect pred;
 protected:
  dependent_node(node_id t, property const &p): result_node(t, p) {}
  void insert_pred(node *n) { pred.push_back(n); }
 public:
  virtual node_vect const &get_subproofs() const { return pred; }
};

struct modus_node: public dependent_node {
  modus_node(int nb, node *nodes[], node *n);
};

struct proof_handler {
  proof_scheme_list *ordered_schemes;
  property_vect goals;
  void operator()() const;
};

class graph_t {
  graph_t *father;
  node_set nodes;		// nodes owned by the graph, each node is implied by hyp
  node_set axioms;		// unusuable axioms (not implied by hyp)
  node_map known_reals;		// best node implied by hyp for each real
  property_vect hyp;		// hypotheses of the graph (they imply the hypotheses from the super-graph)
 public:
  proof_handler prover;
  void insert(node *n) { nodes.insert(n); }
  void remove(node *n) { nodes.erase (n); }
  void insert_axiom(node *);
  void remove_axiom(node *n) { axioms.erase(n); }
  graph_t(graph_t *, property_vect const &);
  ~graph_t();
  node *find_already_known(ast_real const *) const;
  node_vect find_useful_axioms(ast_real const *);
  bool is_useful(property const &) const;
  bool try_real(node *);
  property_vect const &get_hypotheses() const { return hyp; }
  void revalidate_known_reals();
};

extern graph_t *top_graph;
extern node_vect *top_layer;

struct graph_loader {
  graph_t *old_graph;
  graph_loader(graph_t *g) { old_graph = top_graph; top_graph = g; }
  ~graph_loader() { top_graph = old_graph; }
};

struct graph_stacker: graph_loader {
  graph_stacker(property_vect const &h): graph_loader(new graph_t(top_graph, h)) {}
  void clear() { delete top_graph; top_graph = NULL; }
};

struct graph_layer {
  node_vect *old_layer;
  graph_layer() { old_layer = top_layer; top_layer = new node_vect; }
  ~graph_layer();
  void flatten() { delete top_layer; top_layer = NULL; }
};

#endif // PROOFS_PROOF_GRAPH_HPP
