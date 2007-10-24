#include "backends/backend.hpp"

std::ostream *out;

typedef std::map< std::string, backend * > backend_map;
static backend_map backends;

backend::backend(std::string const &name) {
  backends[name] = this;
}

backend *backend::find(std::string const &name) {
  backend_map::const_iterator i = backends.find(name);
  if (i == backends.end()) return NULL;
  return i->second;
}

std::string composite(char prefix, int num) {
  std::ostringstream s;
  s << prefix << (num < 0 ? -num : num);
  return s.str();
}
