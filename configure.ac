AC_INIT([Gappa], [0.4.0],
        [Guillaume Melquiond <guillaume.melquiond@ens-lyon.fr>],
        [gappa])
AM_INIT_AUTOMAKE
AC_PROG_CXX
AC_PROG_LEX
AC_PROG_YACC
AC_PROG_INSTALL
AC_CHECK_LIB(gmp, __gmpz_init)
AC_CHECK_LIB(mpfr, mpfr_add)
AC_CONFIG_HEADER(config.h)
AC_CONFIG_FILES([Makefile src/Makefile])
AC_OUTPUT
