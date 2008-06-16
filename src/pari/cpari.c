/*
 * CLISP interface to PARI <http://pari.math.u-bordeaux.fr/>
 * Copyright (C) 1995 Michael Stoll
 * Copyright (C) 2004-2007 Sam Steingold
 * This is free software, distributed under the GNU GPL
 */

#include "clisp.h"
#include "config.h"
#undef T
#include <pari/pari.h>
#include "cpari.h"

/* we could also use DEF-CALL-OUT, but this is faster, smaller,
   and accommodates the "const" arguments better
   (CLISP FFI does not produce "const" argument declarations) */
void clispPutc(char c);
void clispPutc(char c) {
  pushSTACK(int_char(c)); pushSTACK(Symbol_value(S(standard_output)));
  funcall(L(write_char),2);
}
void clispPuts(const char *s);
void clispPuts(const char *s) {
  pushSTACK(asciz_to_string(s,GLO(foreign_encoding)));
  pushSTACK(Symbol_value(S(standard_output)));
  funcall(L(write_string),2);
}
void clispFlush(void);
void clispFlush(void) {
  pushSTACK(Symbol_value(S(standard_output)));
  funcall(L(finish_output),1);
}

void clispErrPutc(char c);
void clispErrPutc(char c) {
  pushSTACK(int_char(c)); pushSTACK(Symbol_value(S(error_output)));
  funcall(L(write_char),2);
}
void clispErrPuts(const char *s);
void clispErrPuts(const char *s) {
  pushSTACK(asciz_to_string(s,GLO(foreign_encoding)));
  pushSTACK(Symbol_value(S(error_output)));
  funcall(L(write_string),2);
}
void clispErrFlush(void);
void clispErrFlush(void) {
  pushSTACK(Symbol_value(S(error_output)));
  funcall(L(finish_output),1);
}
void clispErrDie(void);
void clispErrDie(void) {
  error(error_condition,GETTEXT("Internal PARI error."));
}

PariOUT clispOut = {clispPutc, clispPuts, clispFlush, NULL};
PariOUT clispErr = {clispErrPutc, clispErrPuts, clispErrFlush, clispErrDie};

void *clispTemp; /* a foreign place to use for casts and accesses from CLISP */

void init_for_clisp (long parisize, long maxprime)
{
#if defined(HAVE_PARI_INIT_OPTS)
  pari_init_opts(parisize,maxprime,0);
#elif defined(HAVE_PARI_INIT)
# if defined(HAVE_INIT_OPTS)
  extern ulong init_opts;
  init_opts = 0;
# endif
  pari_init(parisize,maxprime);
#endif
  pari_outfile = stdout; errfile = stderr; logfile = NULL; infile = stdin;
  pariOut = &clispOut; pariErr = &clispErr;
}

void fini_for_clisp (int leaving)
{
#if defined(HAVE_FREEALL)
  freeall();
#endif
#if defined(HAVE_KILLALLFILES)
  killallfiles(leaving);
#endif
}
