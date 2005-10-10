AC_INIT([Gappa], [0.4.99],
        [Guillaume Melquiond <guillaume.melquiond@ens-lyon.fr>],
        [gappa])
AM_INIT_AUTOMAKE
AC_PROG_CXX
AC_PROG_LEX
AC_PROG_YACC
AC_PROG_INSTALL


XSLTPROC=xsltproc
AC_ARG_WITH([xsltproc], AS_HELP_STRING([--with-xsltproc=PATH], [location of the xsltproc binary]),
	[XSLTPROC="$withval"])
AC_SUBST([XSLTPROC])

DVI2BITMAP=dvi2bitmap
AC_ARG_WITH([dvi2bitmap], AS_HELP_STRING([--with-dvi2bitmap=PATH], [location of the dvi2bitmap binary]),
	[DVI2BITMAP="$withval"])
AC_SUBST([DVI2BITMAP])


AC_LANG(C++)
AC_CHECK_LIB(gmp, __gmpz_init)
AC_CHECK_LIB(mpfr, mpfr_greater_p)

AC_MSG_CHECKING([for Boost (>=1.32)])
AC_TRY_COMPILE([#include <boost/version.hpp>], [
#if BOOST_VERSION >= 103200
#else
#  error Boost version is too old
#endif], [AC_MSG_RESULT(yes)], [AC_MSG_RESULT([no])
AC_MSG_ERROR([Boost not found, bailing out])])

AC_CONFIG_HEADER(config.h)
AC_CONFIG_FILES([Makefile doc/Makefile src/Makefile testsuite/Makefile])
AC_OUTPUT
