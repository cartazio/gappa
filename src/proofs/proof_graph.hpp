#ifndef PROOFS_PROOF_GRAPH_HPP
#define PROOFS_PROOF_GRAPH_HPP

#include "proofs/property.hpp"
#include <map>
#include <set>
#include <vector>

enum node_id { HYPOTHESIS, CONCLUSION, THEOREM, MODUS, UNION, OTHER };

struct node;
struct graph_t;

typedef std::vector< node * > node_vect;
typedef std::set< node * > node_set;
typedef std::map< ast_real const *, node * > node_map;

struct node
{
  property_vect hyp;
  property res;
  node_vect pred;
  node_id type;
  node(node_id t);
  virtual ~node() {}
  void insert_pred(node *);
};

struct graph_t
{
  node *find_compatible_node(property_vect const &hyp, property const &res) const;
  bool has_compatible_hypothesis(ast_real const *) const;
  void insert(node *);
  void erase(node *);
  graph_t(): father(NULL) {}
  graph_t *father;
  node_set nodes;
  node *find_in_cache(property_vect const &hyp, property const &res) const;
  node_map cache;
  property_vect cache_dom;
};

struct graph_storage
{
  graph_storage(): stored_graph(NULL) {}
  ~graph_storage();
  graph_t *stored_graph;
};

struct graph_layer
{
  graph_layer(property_vect const &);
  ~graph_layer();
  void flatten() const;
  void store(graph_storage &) const;
};

extern node_set conclusions;
extern graph_t *graph;
extern graph_t base_graph;

#endif // PROOFS_PROOF_GRAPH_HPP
