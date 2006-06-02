#include <iostream>
#include <string>
#include "../config.h"
#include "backends/backend.hpp"

int parameter_internal_precision = 60;
int parameter_dichotomy_depth = 100;
bool parameter_rfma = false;
bool parameter_constrained = true;
bool parameter_statistics = false;
bool warning_dichotomy_failure = true;
bool warning_hint_difference = true;
bool warning_null_denominator = true;
bool warning_unbound_variable = true;
backend_register const *proof_generator = NULL;

static void help() {
  std::cerr <<
    "Usage: gappa [OPTIONS]\n"
    "Read a statement on standard input and display its proof on standard output.\n"
    "\n"
    "  -h, --help                      display this help and exit\n"
    "  -v, --version                   output version information and exit\n"
    "\n"
    "Engine parameters:\n"
    "  -Eprecision=int                 internal precision (default: " << parameter_internal_precision << ")\n"
    "  -Edichotomy=int                 dichotomy depth (default: " << parameter_dichotomy_depth << ")\n"
    "  -E[no-]reverted-fma             change fma(a,b,c) from a*b+c to c+a*b\n"
    "\n"
    "Engine modes:\n"
    "  -Munconstrained                 do not check for theorem constraints\n"
    "  -Mstatistics                    display statistics at the end\n"
    "\n"
    "Warnings: (default: all)\n"
    "  -W[no-]dichotomy-failure\n"
    "  -W[no-]hint-difference\n"
    "  -W[no-]null-denominator\n"
    "  -W[no-]unbound-variable\n"
    "\n"
    "Backend:\n"
    "  -Bnull                          do not generate a proof (default)\n"
    "  -Bcoq                           produce a script for the Coq proof checker\n";
}

// return false for an unrecognized option
bool parse_option(std::string const &s, bool internal) {
  if (s.size() < 2 || s[0] != '-') return false;
  switch (s[1]) {
  case 'E': {
    std::string::size_type p = s.find('=');
    if (p == std::string::npos) {
      bool yes = s.size() <= 6 || s.substr(2, 3) != "no-";
      std::string o = s.substr(yes ? 2 : 5);
      if (o == "reverted-fma") parameter_rfma = yes;
      else return false;
    } else {
      std::string o = s.substr(2, p - 2), v = s.substr(p + 1);
      int *param;
      if (o == "precision") param = &parameter_internal_precision; else
      if (o == "dichotomy") param = &parameter_dichotomy_depth;
      else return false;
      *param = atoi(v.c_str()); 
    }
    break; }
  case 'M': {
    if (internal) return false;
    std::string o = s.substr(2);
    if (o == "unconstrained") parameter_constrained = false; else
    if (o == "statistics")    parameter_statistics  = true;
    else return false;
    break;
  }
  case 'W': {
    bool yes = s.size() <= 6 || s.substr(2, 3) != "no-";
    std::string o = s.substr(yes ? 2 : 5);
    if (o == "dichotomy-failure") warning_dichotomy_failure = yes; else
    if (o == "hint-difference"  ) warning_hint_difference   = yes; else
    if (o == "null-denominator" ) warning_null_denominator  = yes; else
    if (o == "unbound-variable" ) warning_unbound_variable  = yes;
    else return false;
    break; }
  case 'B': {
    if (internal) return false;
    std::string o = s.substr(2);
    if (o == "null") proof_generator = NULL;
    else {
      proof_generator = backend_register::find(o);
      if (!proof_generator) return false;
    }
    break; }
  default:
    return false;
  }
  return true;
}

// return true if the program can go on
bool parse_args(int argc, char **argv) {
  for(int i = 1; i < argc; ++i) {
    std::string s = argv[i];
    if (parse_option(s, false)) continue;
    if (s == "-v" || s == "--version")
      std::cout << PACKAGE_STRING << '\n';
    else {
      if (s != "-h" && s != "--help")
        std::cerr << "Error: unrecognized option '" << s << "'.\n\n";
      help();
    }
    return false;
  }
  return true;
}
