#ifndef UTILS_HPP
#define UTILS_HPP

#define RUN_ONCE(name) \
  struct class_##name { class_##name(); }; \
  static class_##name dummy_##name; \
  class_##name::class_##name()

#endif // UTILS_HPP
