#ifndef BACKENDS_BACKEND_HPP
#define BACKENDS_BACKEND_HPP

#include <ostream>
#include <string>

struct node;
struct ast_real;

struct backend {
  std::ostream &out;
  backend(std::ostream &o): out(o) {}
  virtual void axiom() = 0;
  virtual std::string rewrite(ast_real const *, ast_real const *) = 0;
  virtual void theorem(node *) = 0;
  virtual ~backend() {}
};

class backend_register {
 protected:
  backend_register(std::string const &);
  virtual ~backend_register() {}
 public:
  virtual backend *create(std::ostream &) const = 0;
  static backend_register const *find(std::string const &);
};

#define REGISTER_BACKEND(name) \
  struct name##_backend_register: backend_register { \
    name##_backend_register(): backend_register(#name) {} \
    virtual backend *create(std::ostream &out) const { return new name##_backend(out); } \
  }; \
  static name##_backend_register dummy;

#endif // BACKENDS_BACKEND_HPP
