#ifndef NUMBERS_INTERVAL_HPP
#define NUMBERS_INTERVAL_HPP

struct interval_base;
struct number;

struct interval {
 //private:
  mutable interval_base const *base;
  interval(interval_base const *b): base(b) {}
 //public:
  interval(): base(0) {}
  interval(number const &, number const &);
  ~interval();
  interval(interval const &);
  interval &operator=(interval const &);
  interval_base *unique() const;
  bool operator<=(interval const &) const;
};

inline bool is_defined(interval const &u) { return u.base; }
bool is_singleton(interval const &);
bool contains_zero(interval const &);
bool is_zero(interval const &);
interval zero();

#endif // NUMBERS_INTERVAL_HPP
