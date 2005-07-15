#include "numbers/interval_utility.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

#include <iostream>

extern int yyparse(void);
extern std::vector< graph_t * > graphs;
extern void coq_display(std::ostream &stream, node_vect const &nodes);

int main() {
  yyparse();
  for(std::vector< graph_t * >::const_iterator i = graphs.begin(), i_end = graphs.end(); i != i_end; ++i) {
    graph_t *g = *i;
    graph_loader loader(g);
    property_vect const &goals = g->get_goals();
    int nb = goals.size();
    std::vector< bool > scheme_results(nb);
    {
      ast_real_vect reals;
      for(int j = 0; j < nb; ++j)
        reals.push_back(goals[j].real);
      g->helper = generate_proof_helper(reals);
      for(int j = 0; j < nb; ++j)
        scheme_results[j] = reals[j];
    }
    std::cerr << "\n\n";
    if (g->populate()) {
      node_vect results(nb);
      std::cerr << "Hypotheses are in contradiction, any result is true.\n";
      coq_display(std::cout, node_vect(1, g->get_contradiction()));
    } else {
      node_vect results(nb);
      for(int j = 0; j < nb; ++j) {
        node *n = find_proof(goals[j]);
        results[j] = n;
        if (!n) {
          std::cerr << "No " << (scheme_results[j] ? "proof" : "path")
                    << " for " << dump_real(goals[j].real) << '\n';
          continue;
        }
        property const &p = n->get_result();
        std::cerr << dump_real(p.real) << " in " << p.bnd << '\n';
      }
      coq_display(std::cout, results);
    }
    delete g;
  }
  return 0;
}
