AC_INIT([Gappa], [0.16.1],
        [Guillaume Melquiond <guillaume.melquiond@inria.fr>],
        [gappa])
AM_INIT_AUTOMAKE
AC_PROG_CXX
AC_PROG_LEX
AC_PROG_YACC
AC_PROG_INSTALL


XSLTPROC=xsltproc
AC_ARG_WITH([xsltproc], AS_HELP_STRING([--with-xsltproc=PATH], [location of the xsltproc binary (documentation)]),
	[XSLTPROC="$withval"])
AC_SUBST([XSLTPROC])

DVI2BITMAP=dvi2bitmap
AC_ARG_WITH([dvi2bitmap], AS_HELP_STRING([--with-dvi2bitmap=PATH], [location of the dvi2bitmap binary (documentation)]),
	[DVI2BITMAP="$withval"])
AC_SUBST([DVI2BITMAP])

DBLATEX=dblatex
AC_ARG_WITH([dblatex], AS_HELP_STRING([--with-dblatex=PATH], [location of the dblatex binary (documentation)]),
	[DBLATEX="$withval"])
AC_SUBST([DBLATEX])

AC_LANG(C++)
AC_CHECK_LIB(gmp, __gmpz_init, ,
AC_MSG_ERROR([ *** Unable to find GMP library (http://www.swox.com/gmp/)]))
AC_CHECK_LIB(mpfr, mpfr_snprintf, ,
AC_MSG_ERROR([ *** Unable to find MPFR (>=2.4) library (http://www.mpfr.org/)]))

AC_MSG_CHECKING([for Boost (>=1.32)])
AC_TRY_COMPILE([#include <boost/version.hpp>], [
#if BOOST_VERSION >= 103200
#else
#  error Boost version is too old
#endif], [AC_MSG_RESULT([yes])], [AC_MSG_RESULT([no])
AC_MSG_ERROR([ *** Unable to find Boost library (http://www.boost.org/)])])

AC_MSG_CHECKING([for tr1/unordered_map])
AC_TRY_COMPILE([#include <tr1/unordered_map>], [
std::tr1::unordered_map<int, double> toto],
[AC_MSG_RESULT([yes])
AC_DEFINE([HAVE_UMAP], [1], [Define to 1 if your Standard Library supports tr1/unordered_map.])], [AC_MSG_RESULT([no])])

AC_CONFIG_HEADERS(config.h)
AC_CONFIG_FILES([Makefile doc/Makefile src/Makefile testsuite/Makefile])
AC_OUTPUT
