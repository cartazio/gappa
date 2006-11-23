#ifndef BACKENDS_BACKEND_HPP
#define BACKENDS_BACKEND_HPP

#include <ostream>
#include <sstream>
#include <string>

struct node;
struct ast_real;

struct backend {
  backend(std::string const &);
  virtual void initialize(std::ostream &) = 0;
  virtual std::string rewrite(ast_real const *, ast_real const *) = 0;
  virtual std::string theorem(node *) = 0;
  virtual void finalize() = 0;
  virtual ~backend() {}
  static backend *find(std::string const &);
};

extern std::ostream *out;

struct auto_flush: std::ostringstream {
  ~auto_flush() { *::out << str(); }
};

#endif // BACKENDS_BACKEND_HPP
