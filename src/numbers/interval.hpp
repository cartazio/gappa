#ifndef NUMBERS_INTERVAL_HPP
#define NUMBERS_INTERVAL_HPP

struct interval_description;
struct interval_real_description;

struct interval {
  interval_description const *desc;
  void *ptr;
  interval();
  interval(interval_description const *);
  interval(interval_description const *, void *);
  interval(interval const &);
  interval &operator=(interval const &);
  ~interval();
};

struct interval_real: interval {
  interval_real();
  interval_real(void *);
  interval_real(interval_real const &);
  interval_real &operator=(interval_real const &);
};

#endif // NUMBERS_INTERVAL_HPP
