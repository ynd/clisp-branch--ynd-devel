dnl Copyright (C) 1993-2002 Free Software Foundation, Inc.
dnl This file is free software, distributed under the terms of the GNU
dnl General Public License.  As a special exception to the GNU General
dnl Public License, this file may be distributed as part of a program
dnl that contains a configuration script generated by Autoconf, under
dnl the same distribution terms as the rest of that program.

dnl From Bruno Haible, Marcus Daniels.

AC_PREREQ(2.13)

AC_DEFUN([CL_GLOBAL_CONSTRUCTORS],
[AC_REQUIRE([CL_AS_UNDERSCORE])dnl
if test -n "$GCC"; then
AC_CACHE_CHECK(for the global constructors function prefix,
cl_cv_cplusplus_ctorprefix, [
cat > conftest.cc << EOF
struct foo { foo (); };
foo foobar;
EOF
# look for the assembly language name in the .s file
AC_TRY_COMMAND(${CXX-g++} $CXXFLAGS -S conftest.cc) >/dev/null 2>&1
if grep '_GLOBAL_\$I\$foobar' conftest.s >/dev/null ; then
  cl_cv_cplusplus_ctorprefix='_GLOBAL_$I$'
else
  if grep '_GLOBAL_\.I\.foobar' conftest.s >/dev/null ; then
    cl_cv_cplusplus_ctorprefix='_GLOBAL_.I.'
  else
    if grep '_GLOBAL__I_foobar' conftest.s >/dev/null ; then
      cl_cv_cplusplus_ctorprefix='_GLOBAL__I_'
    else
      cl_cv_cplusplus_ctorprefix=unknown
    fi
  fi
fi
rm -f conftest*
])
if test "$cl_cv_cplusplus_ctorprefix" '!=' unknown; then
  ac_value='"'"$cl_cv_cplusplus_ctorprefix"'"'
  AC_DEFINE_UNQUOTED(CL_GLOBAL_CONSTRUCTOR_PREFIX,$ac_value)
AC_CACHE_CHECK(for the global destructors function prefix,
cl_cv_cplusplus_dtorprefix, [
cat > conftest.cc << EOF
struct foo { foo (); ~ foo (); };
foo foobar;
EOF
# look for the assembly language name in the .s file
AC_TRY_COMMAND(${CXX-g++} $CXXFLAGS -S conftest.cc) >/dev/null 2>&1
if grep '_GLOBAL_\$D\$foobar' conftest.s >/dev/null ; then
  cl_cv_cplusplus_dtorprefix='_GLOBAL_$D$'
else
  if grep '_GLOBAL_\.D\.foobar' conftest.s >/dev/null ; then
    cl_cv_cplusplus_dtorprefix='_GLOBAL_.D.'
  else
    if grep '_GLOBAL__D_foobar' conftest.s >/dev/null ; then
      cl_cv_cplusplus_dtorprefix='_GLOBAL__D_'
    else
      cl_cv_cplusplus_dtorprefix=none
    fi
  fi
fi
rm -f conftest*
])
  if test "$cl_cv_cplusplus_dtorprefix" '!=' none; then
    ac_value='"'"$cl_cv_cplusplus_ctorprefix"'"'
    AC_DEFINE_UNQUOTED(CL_GLOBAL_DESTRUCTOR_PREFIX,$ac_value)
  fi
dnl Check whether the global constructors/destructors functions are file-scope
dnl only by default. This is the case in egcs-1.1.2 or newer.
AC_CACHE_CHECK(whether the global constructors function need to be exported,
cl_cv_cplusplus_ctorexport, [
cat > conftest1.cc << EOF
struct foo { foo (); };
foo foobar;
EOF
cat > conftest2.cc << EOF
#include "confdefs.h"
#ifdef ASM_UNDERSCORE
#define ASM_UNDERSCORE_PREFIX "_"
#else
#define ASM_UNDERSCORE_PREFIX ""
#endif
struct foo { foo (); };
foo::foo () {}
extern "C" void ctor (void) __asm__ (ASM_UNDERSCORE_PREFIX CL_GLOBAL_CONSTRUCTOR_PREFIX "foobar");
int main() { ctor(); return 0; }
EOF
if AC_TRY_COMMAND(${CXX-g++} -o conftest${ac_exeext} $CXXFLAGS $CPPFLAGS $LDFLAGS conftest1.cc conftest2.cc $LIBS 1>&5) >/dev/null 2>&1 && test -s conftest${ac_exeext}; then
  cl_cv_cplusplus_ctorexport=no
else
  cl_cv_cplusplus_ctorexport=yes
fi
rm -f conftest*
])
if test "$cl_cv_cplusplus_ctorexport" = yes; then
  AC_DEFINE(CL_NEED_GLOBALIZE_CTORDTOR)
fi
fi
fi
])
