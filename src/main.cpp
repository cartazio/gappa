#include <iostream>
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

extern int yyparse(void);
extern std::vector< graph_t * > graphs;
extern bool parse_args(int argc, char **argv);
extern backend_register const *proof_generator;
backend *display = NULL;

struct null_backend: backend {
  null_backend(): backend(std::cout) {}
  virtual void axiom() {}
  virtual std::string rewrite(ast_real const *, ast_real const *) { return std::string(); }
  virtual void theorem(node *) {}
};

int main(int argc, char **argv) {
  if (!parse_args(argc, argv)) return 0;
  if (proof_generator) display = proof_generator->create(std::cout);
  else display = new null_backend;
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
      std::cerr << "Warning: Hypotheses are in contradiction, any result is true.\n";
      display->theorem(g->get_contradiction());
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
      for(node_vect::const_iterator i = results.begin(), end = results.end(); i != end; ++i)
        if (*i) display->theorem(*i);
    }
    delete g;
  }
  delete display;
  return 0;
}
