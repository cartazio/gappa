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
dichotomy_sequence dichotomies;
context_vect contexts;
context const *current_context = NULL;

struct null_backend: backend {
  null_backend(): backend(std::cout) {}
  virtual std::string rewrite(ast_real const *, ast_real const *) { return std::string(); }
  virtual void theorem(node *) {}
};

int main(int argc, char **argv) {
  if (!parse_args(argc, argv)) return 0;
  if (proof_generator) display = proof_generator->create(std::cout);
  else display = new null_backend;
  if (yyparse()) return EXIT_FAILURE;
  ast_real_vect missing_paths = generate_proof_paths();
  for(ast_real_vect::const_iterator i = missing_paths.begin(), i_end = missing_paths.end(); i != i_end; ++i)
    std::cerr << "Warning: no path for " << dump_real(*i) << '\n';
  for(context_vect::const_iterator i = contexts.begin(), i_end = contexts.end(); i != i_end; ++i) {
    current_context =&*i;
    property_vect const &hyp = current_context->hyp;
    graph_t *g = new graph_t(NULL, hyp);
    graph_loader loader(g);
    std::cerr << "\nResults";
    if (unsigned nb_hyp = hyp.size()) {
      std::cerr << " for ";
      for(unsigned i = 0; i < nb_hyp; ++i) {
        if (i != 0) std::cerr << " and ";
        std::cerr << dump_real(hyp[i].real.real()) << " in " << hyp[i].bnd();
      }
    }
    std::cerr << ":\n";
    if (g->populate(dichotomies)) {
      std::cerr << "Warning: hypotheses are in contradiction, any result is true.\n";
      display->theorem(g->get_contradiction());
    } else {
      property_vect const &goals = current_context->goals;
      int nb = goals.size();
      for(int j = 0; j < nb; ++j) {
        node *n = find_proof(goals[j]);
        if (!n) {
          std::cerr << "No proof for " << dump_real(goals[j].real.real()) << '\n';
          continue;
        }
        property const &p = n->get_result();
        std::cerr << dump_real(p.real.real()) << " in " << p.bnd() << '\n';
        display->theorem(n);
      }
    }
    delete g;
  }
  #ifdef LEAK_CHECKER
  delete display;
  #endif
  return EXIT_SUCCESS;
}
