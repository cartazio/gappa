#ifndef NUMBERS_INTERVAL_HPP
#define NUMBERS_INTERVAL_HPP

struct interval_description;

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

#endif // NUMBERS_INTERVAL_HPP
