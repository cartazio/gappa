#ifndef PROOF_GRAPH_HPP
#define PROOF_GRAPH_HPP

#include <vector>
#include <set>
#include "property.hpp"

enum node_id { HYPOTHESIS, CONCLUSION, THEOREM, MODUS, UNION };

struct node;

typedef std::vector< node * > node_vect;
typedef std::set< node * > node_set;

struct node {
  property_vect hyp;
  property res;
  node_vect pred;
  node_set succ;
  node_id type;
  node(node_id t);
  ~node();
  void insert_pred(node *);
  void insert_succ(node *);
  void remove_succ(node *);
  void replace_pred(node *, node *);
};

/*
struct modus_node: node {

};

struct union_node: node {

};
*/

struct graph_t {
  node *find_compatible_node(property_vect const &hyp, property const &res) const;
  node_set const &get_conclusions() const { return conclusions; }
  void insert(node *);
  void erase(node *);
 private:
  node_set nodes;
  node_set conclusions;
};

extern graph_t graph;

#endif // PROOF_GRAPH_HPP
