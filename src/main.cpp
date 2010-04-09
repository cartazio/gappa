#include <iostream>

#include "parameters.hpp"
#include "backends/backend.hpp"
#include "numbers/interval_utility.hpp"
#include "parser/ast.hpp"
#include "proofs/proof_graph.hpp"
#include "proofs/schemes.hpp"

extern bool
  parameter_constrained, parameter_statistics, parameter_sequent;
extern int yyparse(void);
extern bool detailed_io;
extern backend *proof_generator;
dichotomy_sequence dichotomies;
property_tree current_goals;
context goal;
bool goal_reduction = true;

extern int
  stat_tested_th, stat_successful_th,
  stat_tested_real, stat_discarded_real,
  stat_intersected_pred, stat_discarded_pred;

void display_context(context const &ctx)
{
  property_vect const &hyp = ctx.hyp;
  if (parameter_sequent)
  {
    std::cerr << "\nScript:\n";
    for(unsigned i = 0, nb_hyp = hyp.size(); i < nb_hyp; ++i) {
      std::cerr << "  " << dump_property_nice(hyp[i])
                << (i != nb_hyp - 1 ? " /\\\n" : " ->\n");
    }
    std::cerr << "  " << dump_prop_tree_nice(ctx.goals) << "\nResults:\n";
  }
  else
  {
    std::cerr << "\nResults";
    if (unsigned nb_hyp = hyp.size()) {
      std::cerr << " for ";
      for(unsigned i = 0; i < nb_hyp; ++i) {
        if (i != 0) std::cerr << " and ";
        std::cerr << dump_real_short(hyp[i].real) << " in " << hyp[i].bnd();
      }
    }
    std::cerr << ":\n";
  }
}

int main(int argc, char **argv)
{
  parse_args_status pargs_status = parse_args(argc, argv);
  if (pargs_status != PARGS_CONTINUE)
    return pargs_status == PARGS_FAILURE ? EXIT_FAILURE : EXIT_SUCCESS;
  if (proof_generator) {
    if (!parameter_constrained) {
      std::cerr << "Error: unconstrained mode is not compatible with script generation, since proofs are left incomplete.\n";
      return EXIT_FAILURE;
    }
    proof_generator->initialize(std::cout);
    goal_reduction = false;
  }
  if (yyparse()) return EXIT_FAILURE;
  preal_vect missing_paths = generate_proof_paths();
  for (preal_vect::const_iterator i = missing_paths.begin(),
       i_end = missing_paths.end(); i != i_end; ++i)
  {
    std::cerr << "Warning: no path was found for " << dump_real_short(*i) << ".\n";
  }
  bool globally_proven = true;
  {
    context const &current_context = goal;
    if (proof_generator) proof_generator->reset();
    graph_t *g = new graph_t(NULL, current_context.hyp);
    g->populate(current_context.goals, property_tree(), dichotomies, 100*1000*1000);
    if (node *n = g->get_contradiction())
    {
      display_context(current_context);
      if (!goal_reduction) {
        if (!current_context.goals.empty())
          std::cerr << "Warning: hypotheses are in contradiction, any result is true.\n";
        else
          std::cerr << "A contradiction was built from the hypotheses.\n";
      }
      if (proof_generator) {
        enlarger(node_vect(1, n));
        proof_generator->theorem(n);
      }
      g->show_dangling();
    } else if (current_context.goals.empty()) {
      display_context(current_context);
      std::cerr << "Warning: no contradiction was found.\n";
      globally_proven = false;
    } else {
      node_vect nodes;
      property_tree pt = current_context.goals;
      pt.get_nodes(g, nodes);
      if (proof_generator) enlarger(nodes);
      typedef std::map< std::string, node * > named_nodes;
      named_nodes results;
      for (node_vect::const_iterator j = nodes.begin(),
           j_end = nodes.end(); j != j_end; ++j)
      {
        node *n = *j;
        assert(n->type == GOAL);
        results[dump_real_short(n->get_result().real)] = n;
      }
      display_context(current_context);
      for (named_nodes::const_iterator j = results.begin(),
           j_end = results.end(); j != j_end; ++j)
      {
        node *n = j->second;
        detailed_io = true;
        std::cerr << j->first << " in " << n->get_result().bnd() << '\n';
        detailed_io = false;
        if (proof_generator) proof_generator->theorem(n);
      }
      if (!pt.empty()) {
        std::cerr << "Warning: some enclosures were not satisfied.\n"
          "Missing ";
        std::cerr << dump_prop_tree(pt) << '\n';
        globally_proven = false;
      }
      g->show_dangling();
    }
    delete g;
  }
  if (proof_generator) proof_generator->finalize();
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
