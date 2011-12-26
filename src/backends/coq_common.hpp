/*
   Copyright (C) 2004 - 2012 by Guillaume Melquiond <guillaume.melquiond@inria.fr>
   Part of the Gappa tool http://gappa.gforge.inria.fr/

   This program is free software; you can redistribute it and/or modify
   it under the terms of the CeCILL Free Software License Agreement or
   under the terms of the GNU General Public License version.

   See the COPYING and COPYING.GPL files for more details.
*/

#include <map>
#include <string>

class number;
class interval;

namespace coq {

typedef std::map<std::string, char const *> theorem_map;
extern theorem_map theorems;

/** Use fully-qualified names for Coq identifiers. */
extern bool fqn;

/** Use vernacular for definitions. */
extern bool vernac;

std::string convert_name(std::string const &name);
std::string display(number const &f);
std::string display(interval const &i);
}
