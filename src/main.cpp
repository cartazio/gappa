/*
   Copyright (C) 2004 - 2010 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

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
property_tree context;
bool goal_reduction = true;

extern int
  stat_tested_real, stat_discarded_real,
  stat_tested_theo, stat_discarded_theo,
  stat_tested_app, stat_successful_app,
  stat_intersected_pred, stat_discarded_pred;

#if 0
void display_context(context const &ctx)
{
  property_vect const &hyp = ctx.hyp;
  if (parameter_sequent)
  {
    change_io_format dummy(IO_EXACT);
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
        std::cerr << dump_property_nice(hyp[i]);
      }
    }
    std::cerr << ":\n";
  }
}
#endif

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
    std::cerr << "Warning: no path was found for " << dump_real(*i) << ".\n";
  }
  bool globally_proven = true;
  undefined_map umap;
  graph_t *g = new graph_t(NULL, context);
  g->populate(property_tree(), dichotomies, 100*1000*1000, &umap);
  for (undefined_map::const_iterator i = umap.begin(),
       i_end = umap.end(); i != i_end; ++i)
  {
    change_io_format dummy(IO_FULL);
    std::cerr << dump_property_nice(i->second) << '\n';
  }
  if (node *n = g->get_contradiction()) {
    if (proof_generator) {
      enlarger(node_vect(1, n));
      instances = &umap;
      proof_generator->theorem(n);
    }
  } else {
    std::cerr << "Warning: some enclosures were not satisfied.\n";
    globally_proven = false;
  }
  g->show_dangling();
  delete g;
  if (proof_generator) proof_generator->finalize();
  if (parameter_statistics) {
    std::cerr <<
      "Statistics:\n"
      "  " << stat_tested_real << " expressions were considered,\n"
      "    but then " << stat_discarded_real << " of those got discarded.\n"
      "  " << stat_tested_theo << " theorems were considered,\n"
      "    but then " << stat_discarded_theo << " of those got discarded.\n"
      "  " << stat_tested_app << " applications were tried. Among those,\n"
      "    " << stat_successful_app << " were successful,\n"
      "    yet " << stat_discarded_pred << " proved useless\n"
      "    and " << stat_intersected_pred << " improved existing results.\n";
  }
  return globally_proven ? EXIT_SUCCESS : EXIT_FAILURE;
}
