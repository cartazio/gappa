#ifndef ROUND_HPP
#define ROUND_HPP

#include <gmp.h>
#include <mpfr.h>

bool split_exact(mpfr_t const &f, mpz_t &frac, int &exp, bool &sign); // return true if zero

#endif // ROUND_HPP
