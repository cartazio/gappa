#include <map>
#include "backends/backend.hpp"

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
