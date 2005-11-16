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
property_tree current_goals;

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
  std::vector< bool > proven_contexts;
  bool globally_proven = true;
  for(context_vect::const_iterator i = contexts.begin(), i_end = contexts.end(); i != i_end; ++i) {
    context const &current_context = *i;
    current_goals = current_context.goals;
    property_vect const &hyp = current_context.hyp;
    std::cerr << "\nResults";
    if (unsigned nb_hyp = hyp.size()) {
      std::cerr << " for ";
      for(unsigned i = 0; i < nb_hyp; ++i) {
        if (i != 0) std::cerr << " and ";
        std::cerr << dump_real(hyp[i].real.real()) << " in " << hyp[i].bnd();
      }
    }
    std::cerr << ":\n";
    bool deps_satisfied = true;
    for(std::vector< int >::const_iterator j = current_context.deps.begin(),
        j_end = current_context.deps.end(); j != j_end; ++j)
      if (!proven_contexts[*j]) { deps_satisfied = false; break; }
    if (!deps_satisfied) {
      std::cerr << "Warning: generated hypotheses were not proved, skipping.\n";
      continue;
    }
    graph_t *g = new graph_t(NULL, hyp);
    graph_loader loader(g);
    if (g->populate(dichotomies)) {
      if (!current_context.goals.empty())
        std::cerr << "Warning: hypotheses are in contradiction, any result is true.\n";
      display->theorem(g->get_contradiction());
      proven_contexts.push_back(true);
    } else if (current_context.goals.empty()) {
      std::cerr << "Warning: no contradiction was found.\n";
      globally_proven = false;
      proven_contexts.push_back(false);
    } else {
      node_set goals;
      bool proven = current_context.goals.get_reals(goals);
      for(node_set::const_iterator j = goals.begin(), j_end = goals.end(); j != j_end; ++j) {
        node *n = *j;
        property const &p = n->get_result();
        std::cerr << dump_real(p.real.real()) << " in " << p.bnd() << '\n';
        display->theorem(n);
      }
      if (!proven) {
        std::cerr << "Warning: some enclosures were not satisfied.\n";
        globally_proven = false;
      }
      proven_contexts.push_back(proven);
    }
    delete g;
  }
  #ifdef LEAK_CHECKER
  delete display;
  #endif
  return globally_proven ? EXIT_SUCCESS : EXIT_FAILURE;
}
