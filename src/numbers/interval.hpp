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

interval operator+(interval const &, interval const &);
interval operator-(interval const &, interval const &);
interval operator*(interval const &, interval const &);
interval operator/(interval const &, interval const &);

#endif // NUMBERS_INTERVAL_HPP
