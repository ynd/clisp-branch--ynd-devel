# -*- Autoconf -*-
# Copyright (C) 2007-2008 Sam Steingold (GNU GPL2+)

AC_PREREQ(2.61)

AC_DEFUN([CL_FFCALL],[dnl
AC_ARG_WITH([ffcall],
[AC_HELP_STRING([--with-ffcall],[use FFCALL (default is YES, if present)])],
[cl_use_ffcall=$withval],[cl_use_ffcall=default])
if test $cl_use_ffcall != no; then
AC_LIB_FROMPACKAGE(avcall,libffcall)
AC_LIB_FROMPACKAGE(callback,libffcall)
AC_LIB_LINKFLAGS([avcall])
AC_LIB_LINKFLAGS([callback])
AC_CHECK_HEADERS(avcall.h callback.h)
if test "$ac_cv_header_avcall_h" = yes \
     -a "$ac_cv_header_callback_h" = yes
then
cl_save_LIBS="$LIBS"
AC_LIB_APPENDTOVAR([LIBS], [$LIBAVCALL])
AC_LIB_APPENDTOVAR([LIBS], [$LIBCALLBACK])
AC_SEARCH_LIBS(__builtin_avcall)
AC_SEARCH_LIBS(trampoline_r_data0)
if test "$ac_cv_search___builtin_avcall" = no \
     -o "$ac_cv_search_trampoline_r_data0" = no
then LIBS=$cl_save_LIBS
fi
fi
AC_CACHE_CHECK([whether libffcall is installed],[cl_cv_have_ffcall],
[if test "$ac_cv_header_avcall_h" = yes \
      -a "$ac_cv_header_callback_h" = yes \
      -a "$ac_cv_search___builtin_avcall" != no \
      -a "$ac_cv_search_trampoline_r_data0" != no
then cl_cv_have_ffcall=yes
else cl_cv_have_ffcall=no
fi])
if test $cl_use_ffcall = yes -a $cl_cv_have_ffcall = no; then
  FFCALL=ffcall-1.8
  AC_MSG_ERROR([despite --with-ffcall, FFCALL was not found
 Either call configure without --with-ffcall or do
  mkdir tools; cd tools; prefix=`pwd`/${ac_cv_host}
  wget http://ftp.gnu.org/pub/gnu/ffcall/${FFCALL}.tar.gz
  tar xfz ${FFCALL}.tar.gz
  cd ${FFCALL}
  ./configure --prefix=\${prefix} && make && make check && make install
  cd ../..
  ./configure --with-libffcall-prefix=\${prefix} [$]*])
fi
fi;])])
