#ifndef PROOF_GRAPH_HPP
#define PROOF_GRAPH_HPP

#include <vector>
#include <set>
#include "property.hpp"

enum node_id { HYPOTHESIS, CONCLUSION, THEOREM, MODUS, UNION, OTHER };

struct node;
struct graph_t;
struct graph_layer;

typedef std::vector< node * > node_vect;
typedef std::set< node * > node_set;

struct node
{
  property_vect hyp;
  property res;
  node_vect pred;
  node_set succ;
  node_id type;
  node(node_id t);
  virtual ~node() {}
  void insert_pred(node *);
  void insert_succ(node *);
  void remove_succ(node *);
  void replace_pred(node *, node *);
};

struct graph_t
{
  node *find_compatible_node(property_vect const &hyp, property const &res) const;
  void insert(node *);
  void erase(node *);
  graph_t(): father(NULL) {}
  graph_t *father;
 private:
  node_set nodes;
  friend struct graph_layer;
};

struct graph_layer {
  graph_layer();
  ~graph_layer();
  void flatten() const;
};

extern node_set conclusions;
extern graph_t *graph;
extern graph_t base_graph;

#endif // PROOF_GRAPH_HPP
