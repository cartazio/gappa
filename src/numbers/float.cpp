#include "interval.hpp"
#include "round.hpp"

enum rounding_type { ROUND_UP, ROUND_DN, ZOUND_ZR, ROUND_CE };

struct float_rounding_class: rounding_class {
  float_format const *format;
  rounding_type type;
  virtual interval bound(interval const &, char const *&) const;
  virtual interval error(interval const &, char const *&) const;
};

float_format formats[4] = {
  { min_exp: -149,   prec: 24  },
  { min_exp: -1074,  prec: 53  },
  { min_exp: -16445, prec: 64  },
  { min_exp: -16494, prec: 113 }
};
