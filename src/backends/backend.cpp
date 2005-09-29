#include <map>
#include "backend.hpp"

typedef std::map< std::string, backend_register const * > backend_map;
static backend_map backends;

backend_register::backend_register(std::string const &name) {
  backends[name] = this;
}

backend_register const *backend_register::find(std::string const &name) {
  backend_map::const_iterator i = backends.find(name);
  if (i == backends.end()) return NULL;
  return i->second;
}
