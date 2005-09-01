#include <map>
#include <sstream>
#include "parser/ast.hpp"
#include "numbers/interval_arith.hpp"
#include "numbers/interval_utility.hpp"
#include "numbers/real.hpp"
#include "numbers/round.hpp"

struct relative_rounding_class: rounding_class {
  interval he;
  int prec;
  relative_rounding_class(int);
  virtual interval round                      (interval const &, std::string &) const;
  virtual interval relative_error_from_real   (interval const &, std::string &) const;
  virtual interval relative_error_from_rounded(interval const &, std::string &) const;
  virtual std::string name() const;
};

relative_rounding_class::relative_rounding_class(int p): prec(p) {
  he = from_exponent(-p, 0);
}

interval relative_rounding_class::round(interval const &i, std::string &name) const {
  std::ostringstream s;
  s << "(relative_round " << prec << ')';
  name = s.str();
  return i * (interval(number(1), number(1)) + he);
}

interval relative_rounding_class::relative_error_from_real(interval const &, std::string &name) const {
  std::ostringstream s;
  s << "(relative_error " << prec << ')';
  name = s.str();
  return he;
}

interval relative_rounding_class::relative_error_from_rounded(interval const &, std::string &name) const {
  std::ostringstream s;
  s << "(relative_error_inv " << prec << ')';
  name = s.str();
  return he;
}

std::string relative_rounding_class::name() const {
  std::ostringstream s;
  s << "relative " << prec;
  return s.str();
}

typedef std::map< int, rounding_class const * > relative_cache;
static relative_cache cache;

struct relative_rounding_generator: rounding_generator {
  relative_rounding_generator();
  virtual rounding_class const *operator()(rounding_params const &) const;
};

relative_rounding_generator::relative_rounding_generator() {
  ast_ident *id = ast_ident::find("relative");
  id->id_type = REAL_RND;
  id->rnd = this;
}

rounding_class const *relative_rounding_generator::operator()(rounding_params const &p) const {
  if (p.size() != 1) return NULL;
  int prec = p[0];
  relative_cache::const_iterator i = cache.find(prec);
  if (i != cache.end()) return i->second;
  rounding_class const *rnd = new relative_rounding_class(prec);
  cache.insert(std::make_pair(prec, rnd));
  return rnd;
}

static relative_rounding_generator dummy;
