AC_INIT([Gappa], [0.4.4],
        [Guillaume Melquiond <guillaume.melquiond@ens-lyon.fr>],
        [gappa])
AM_INIT_AUTOMAKE
AC_PROG_CXX
AC_PROG_LEX
AC_PROG_YACC
AC_PROG_INSTALL
AC_CHECK_LIB(gmp, __gmpz_init)
AC_CHECK_LIB(mpfr, mpfr_add)
AC_MSG_CHECKING([for Boost (>=1.32)])
AC_TRY_COMPILE([#include <boost/version.hpp>], [
#if BOOST_VERSION >= 103200
#else
#  error Boost version is too old
#endif], [AC_MSG_RESULT(yes)], [AC_MSG_RESULT([no])
AC_MSG_ERROR([Boost not found, bailing out])])

AC_CONFIG_HEADER(config.h)
AC_CONFIG_FILES([Makefile src/Makefile])
AC_OUTPUT
