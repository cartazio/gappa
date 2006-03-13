#include <iostream>
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

extern bool parameter_constrained, parameter_statistics;
extern int yyparse(void);
extern std::vector< graph_t * > graphs;
extern bool parse_args(int argc, char **argv);
extern backend_register const *proof_generator;
extern bool detailed_io;
backend *display = NULL;
dichotomy_sequence dichotomies;
context_vect contexts;
property_tree current_goals;

extern int
  stat_tested_th, stat_successful_th,
  stat_tested_real, stat_discarded_real,
  stat_intersected_pred, stat_discarded_pred;

struct null_backend: backend {
  null_backend(): backend(std::cout) {}
  virtual std::string rewrite(ast_real const *, ast_real const *) { return std::string(); }
  virtual void theorem(node *) {}
};

int main(int argc, char **argv) {
  if (!parse_args(argc, argv)) return 0;
  if (proof_generator) {
    if (!parameter_constrained) {
      std::cerr << "Error: unconstrained mode is not compatible with script generation, since proofs are left incomplete.\n";
      return EXIT_FAILURE;
    }
    display = proof_generator->create(std::cout);
  } else display = new null_backend;
  if (yyparse()) return EXIT_FAILURE;
  ast_real_vect missing_paths = generate_proof_paths();
  for(ast_real_vect::const_iterator i = missing_paths.begin(), i_end = missing_paths.end(); i != i_end; ++i)
    std::cerr << "Warning: no path was found for " << dump_real(*i) << ".\n";
  std::vector< bool > proven_contexts;
  bool globally_proven = true;
  for(context_vect::const_iterator i = contexts.begin(), i_end = contexts.end(); i != i_end; ++i) {
    context const &current_context = *i;
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
    if (g->populate(current_context.goals, dichotomies)) {
      if (!current_context.goals.empty())
        std::cerr << "Warning: hypotheses are in contradiction, any result is true.\n";
      else
        std::cerr << "a contradiction was built from the hypotheses.\n";
      display->theorem(g->get_contradiction());
      proven_contexts.push_back(true);
    } else if (current_context.goals.empty()) {
      std::cerr << "Warning: no contradiction was found.\n";
      globally_proven = false;
      proven_contexts.push_back(false);
    } else {
      node_set nodes;
      bool proven = current_context.goals.get_nodes(g, nodes);
      typedef std::map< std::string, node * > named_nodes;
      named_nodes results;
      for(node_set::const_iterator j = nodes.begin(), j_end = nodes.end(); j != j_end; ++j) {
        node *n = *j;
        results[dump_real(n->get_result().real.real())] = n;
      }
      for(named_nodes::const_iterator j = results.begin(), j_end = results.end(); j != j_end; ++j) {
        node *n = j->second;
        detailed_io = true;
        std::cerr << j->first << " in " << n->get_result().bnd() << '\n';
        detailed_io = false;
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
  delete display;
  if (parameter_statistics) {
    std::cerr <<
      "Statistics:\n"
      "  " << stat_tested_real << " expressions were considered,\n"
      "    but then " << stat_discarded_real << " of these got discarded.\n"
      "  " << stat_tested_th << " theorems were tried. Among these,\n"
      "    " << stat_successful_th << " were successfully instantiated,\n"
      "    yet " << stat_discarded_pred << " of these were not good enough\n"
      "    and " << stat_intersected_pred << " were only partially better.\n";
  }
  return globally_proven ? EXIT_SUCCESS : EXIT_FAILURE;
}
