/*
 * Time measuring functions for CLISP
 * Bruno Haible 1990-2005
 * Sam Steingold 1998-2007
 * German comments and names translated into English: Reini Urban 2007-12
 */

#include "lispbibl.c"
/* for high16, low16 in %%TIME,
   for divu in GET-UNIVERSAL-TIME,
   for mulu32 in GET-INTERNAL-RUN-TIME, GET-INTERNAL-REAL-TIME */
#include "arilev0.c"

/* Main types:
 Decoded time =
   seconds, minutes, hour, day, month, year,
   day-of-week, daylight-saving-time, time zone.
 Universal time =
   seconds since 1900-01-01 */
#ifdef TIME_UNIX_TIMES
  /* Two small bugs:
   - Wrap-around of internal_time_t after many days.
   - LISP clock may be up to 1 sec behind the true clock.
   Internal time =
     1/CLK_TCK sec since session start */
#endif
#ifdef TIME_UNIX
  /* A small bug:
   - %%TIME works only for time differences <= 194 days.
   Internal time =
     microseconds since session start */
#endif
#ifdef TIME_WIN32
  /* A small bug:
   - %%TIME works only for time differences <= 19 days.
   Internal time =
     tenth of microseconds since session start */
#endif

/* ------------------------------------------------------------------------
 *                    Measuring time consumption

 Time consumption is measured with sub-second resolution,
 using internal_time_t. */

/* Variables: */
#ifdef TIME_UNIX_TIMES
  /* (The unit is ca. 1/60 sec or 1/100 sec, a 32 bit counter therefore
   suffices for a long while.) */
#endif
#ifdef TIME_UNIX
  /* The unit is 1 µsec.
   (Independently whether the system clock is 60 Hz or 50 Hz or better.) */
#endif
#ifdef TIME_WIN32
  /* The unit is 0.1 µsec. */
#endif
  /* Running time: */
local internal_time_t realstart_time; /* real time at start of LISP session */
#ifndef HAVE_RUN_TIME
/* Time that the LISP session consumes: */
local uintL run_time = 0;       /* total runtime up to now */
local uintL runstop_time;       /* if the stop watch is running:
                                   the time of the last run-stop change */
local bool run_flag = false; /* true if the stop watch is running */
#endif


#ifdef TIME_RELATIVE

/* Returns the current hi-res time.
 get_time() */
 #ifdef TIME_UNIX_TIMES
/* < uintL result: current value of the CLK_TCK Hz counter */
local uintL get_time(void)
{
  var struct tms buffer;
  return (uintL)times(&buffer);
}
 #endif

#ifndef HAVE_RUN_TIME

/* Stops the swop-watch.
 run_time_stop(); */
global void run_time_stop (void)
{
  if (!run_flag) return;        /* stop-watch already stopped -> OK */
  /* Add the now consumed runtime to the total runtime: */
  run_time += get_time()-runstop_time;
  run_flag = false;             /* stop-watch now stopped */
}

/* Lets the stop-watch run again.
 run_time_restart(); */
global void run_time_restart (void)
{
  if (run_flag) return;         /* stop-watch already running -> OK */
  runstop_time = get_time();    /* save current time */
  run_flag = true;              /* stop-watch now running */
}

#endif

/* Returns the real time counter.
 get_real_time()
 < uintL result: Time since start of LISP session (in 1/50 sec or in 1/100 sec
                 or in 1/CLK_TCK sec) */
global uintL get_real_time (void)
{ return get_time()-realstart_time; }

#endif

#ifdef TIME_UNIX_TIMES

/* Returns the run time counter.
 get_run_time(&runtime);
 < internal_time_t runtime: consumed run time since session start (in ticks)
 < uintL result: same as for get_time() */
global uintL get_run_time (internal_time_t* runtime)
{
  var struct tms tms;
  var uintL now_time;
  begin_system_call();
  now_time = times(&tms);
  end_system_call();
  *runtime = tms.tms_utime + tms.tms_stime; /* user time + system time */
  return now_time;                          /* cf. get_time() */
}

#endif

#ifdef TIME_UNIX

/* Returns the real time counter.
 get_real_time()
 < internal_time_t* result: absolute time */
global void get_real_time (internal_time_t* it)
{
 #ifdef HAVE_GETTIMEOFDAY
  begin_system_call();
  if (long_bitsize == 32
      && sizeof(struct timeval) == sizeof(internal_time_t)
      && offsetof(struct timeval,tv_sec) == offsetof(internal_time_t,tv_sec)
      && offsetof(struct timeval,tv_usec) == offsetof(internal_time_t,tv_usec))
    { /* internal_time_t and struct timeval are effectively the same type. */
    if (gettimeofday((struct timeval *)it,NULL) != 0) { OS_error(); }
  } else {
    /* On some 64-bit platforms, time_t is 64-bit, and struct timeval has
     twice the size than internal_time_t! */
    struct timeval tmp;
    if (gettimeofday(&tmp,NULL) != 0) { OS_error(); }
    it->tv_sec = tmp.tv_sec; it->tv_usec = tmp.tv_usec;
  }
  end_system_call();
 #elif defined(HAVE_FTIME)
  var struct timeb timebuf;
  begin_system_call();
  ftime(&timebuf);
  end_system_call();
  it->tv_sec = timebuf.time;
  it->tv_usec = (uintL)(timebuf.millitm) * (ticks_per_second/1000);
 #endif
}

/* Returns the run time counter.
 get_run_time(&runtime);
 < internal_time_t runtime: consumed run time since session start (in ticks) */
global void get_run_time (internal_time_t* runtime)
{
 #if defined(HAVE_GETRUSAGE)
  var struct rusage rusage;
  begin_system_call();
  if (!( getrusage(RUSAGE_SELF,&rusage) ==0)) { OS_error(); }
  end_system_call();
  /* runtime = user time + system time */
  add_internal_time(rusage.ru_utime,rusage.ru_stime, *runtime);
 #elif defined(HAVE_SYS_TIMES_H)
  var uintL used_time;     /* consumed time, measured in 1/HZ seconds */
  var struct tms tms;
  begin_system_call();
  if (times(&tms) == (clock_t)(-1))
    used_time = 0;             /* times() failed -> used_time unknown */
  else
    used_time = tms.tms_utime + tms.tms_stime; /* user time + system time */
  end_system_call();
  /* Convert to seconds and microseconds: */
  #if !defined(HZ)
   #if defined(CLK_TCK)
    #define HZ CLK_TCK
   #elif defined(CLOCKS_PER_SECOND)
    #define HZ CLOCKS_PER_SECOND
   #else
    #error do not know clock tick length
   #endif
  #endif
  runtime->tv_sec = floor(used_time,HZ);
  runtime->tv_usec = (used_time % HZ) * floor(2*1000000+HZ,2*HZ);
 #endif
}

#endif

#ifdef TIME_WIN32

/* Returns the real time counter.
 get_real_time()
 < internal_time_t* result: absolute time */
global void get_real_time (internal_time_t* it)
{ GetSystemTimeAsFileTime(it); }

/* Returns the run time counter.
 get_run_time(&runtime);
 < internal_time_t runtime: consumed run time since session start (in ticks) */
global void get_run_time (internal_time_t* runtime)
{
  var FILETIME creation_time;
  var FILETIME exit_time;
  var FILETIME kernel_time;
  var FILETIME user_time;
  begin_system_call();
  if (GetProcessTimes(GetCurrentProcess(),&creation_time,&exit_time,
                      &kernel_time,&user_time)) {
    end_system_call();
    /* runtime = User time + Kernel time */
    add_internal_time(user_time,kernel_time, *runtime);
  } else {
    if (!(GetLastError()==ERROR_CALL_NOT_IMPLEMENTED)) { OS_error(); }
    /* GetProcessTimes() is not implemented on Win95. Use get_real_time()
     instead. This is only a crude approximation, I know.
     (We keep HAVE_RUN_TIME defined, so that Win95 users will notice
     that "Run time" and "Real time" are always the same and draw their
     conclusions from it.) */
    end_system_call();
    var internal_time_t real_time;
    get_real_time(&real_time);
    sub_internal_time(real_time,realstart_time, *runtime);
  }
}

#endif

/* Returns the whole set of run time counters.
 get_running_times(&timescore);
 < timescore.runtime:  consumed run time since start of session (in ticks)
 < timescore.realtime: real time since start of session (in ticks)
 < timescore.gctime:   GC time since start of session (in ticks)
 < timescore.gccount:  number of GCs since start of session
 < timescore.gcfreed:  number of reclaimed bytes since start of session */
global void get_running_times (timescore_t* tm)
{
 #ifndef HAVE_RUN_TIME
  var uintL time = get_time();
  tm->realtime = time - realstart_time;
  tm->runtime = (run_flag ?
                 time - runstop_time + run_time : /* stop-watch still running*/
                 run_time);  /* stop-watched stopped */
 #endif
 #ifdef TIME_UNIX
  /* Get real time: */
  var internal_time_t real_time;
  get_real_time(&real_time);
  tm->realtime.tv_sec = real_time.tv_sec - realstart_time.tv_sec;
  tm->realtime.tv_usec = real_time.tv_usec;
  /* Get run time: */
  get_run_time(&tm->runtime);
 #endif
 #ifdef TIME_UNIX_TIMES
  /* Get run time and real time both together: (vgl. get_real_time()) */
  tm->realtime = get_run_time(&tm->runtime) - realstart_time;
 #endif
 #ifdef TIME_WIN32
  /* Get real time: */
  var internal_time_t real_time;
  get_real_time(&real_time);
  sub_internal_time(real_time,realstart_time, tm->realtime);
  /* Get run time: */
  get_run_time(&tm->runtime);
 #endif
  tm->gctime = gc_time;
  tm->gccount = gc_count;
  tm->gcfreed = gc_space;
}

#if TIME_METHOD == 2
/* Converts an internal_time_t to a Lisp integer.
 internal_time_to_I(&it) */
local object internal_time_to_I (const internal_time_t* tp)
{
 #ifdef TIME_UNIX
  /* Convert to microseconds: tp->tv_sec * ticks_per_second + tp->tv_usec */
  #ifdef intQsize
  return UQ_to_I((uintQ)(tp->tv_sec)*ticks_per_second + (uintQ)(tp->tv_usec));
  #else
  var uintL hi;
  var uintL lo;
  mulu32(tp->tv_sec,ticks_per_second, hi=,lo=);
  if ((lo += tp->tv_usec) < tp->tv_usec) { hi += 1; }
  return L2_to_I(hi,lo);
  #endif
 #endif
 #ifdef TIME_WIN32
  return L2_to_I(tp->dwHighDateTime,tp->dwLowDateTime);
 #endif
}
#endif

LISPFUNNR(get_internal_real_time,0)
{ /* (GET-INTERNAL-REAL-TIME), CLTL p. 446 */
 #if TIME_METHOD == 1
  VALUES1(UL_to_I(get_real_time())); /* get real time since start of session */
 #elif TIME_METHOD == 2
  var internal_time_t tp;       /* absolute real time */
  get_real_time(&tp);
  VALUES1(internal_time_to_I(&tp)); /* convert to integer */
 #endif
}

LISPFUNNR(get_internal_run_time,0)
{ /* (GET-INTERNAL-RUN-TIME), CLTL p. 446 */
  var timescore_t tm;
  get_running_times(&tm); /* get run time since start of session */
 #if TIME_METHOD == 1
  VALUES1(UL_to_I(tm.runtime)); /* convert to integer */
 #elif TIME_METHOD == 2
  VALUES1(internal_time_to_I(&tm.runtime)); /* convert to integer */
 #endif
}

/* ------------------------------------------------------------------------
 *                    Converting the system time format */

#ifdef UNIX
/* UP: convert the system time format into Decoded-Time.
 convert_time(&time,&timepoint);
 > time_t time: in system time format
 < timepoint.seconds, timepoint.minutes, timepoint.hours,
   timepoint.day, timepoint.month, timepoint.year. All as fixnums */
global void convert_time (const time_t* time, decoded_time_t* timepoint)
{
  begin_system_call();
  var struct tm * tm = localtime(time); /* decode */
  /* (The OS system time can decode the system time) */
  end_system_call();
  if (tm) { /* localtime was successful */
    timepoint->seconds = fixnum(tm->tm_sec);
    timepoint->minutes = fixnum(tm->tm_min);
    timepoint->hours   = fixnum(tm->tm_hour);
    timepoint->day     = fixnum(tm->tm_mday);
    timepoint->month   = fixnum(1+tm->tm_mon);
    timepoint->year    = fixnum(1900+tm->tm_year);
  } else { /* unsuccessful -> use 1.1.1900, 00:00:00 as default */
    timepoint->seconds = Fixnum_0;
    timepoint->minutes = Fixnum_0;
    timepoint->hours   = Fixnum_0;
    timepoint->day     = Fixnum_1;
    timepoint->month   = Fixnum_1;
    timepoint->year    = fixnum(1900);
  }
}
#endif
#ifdef WIN32_NATIVE
/* UP: convert the system time format into Decoded-Time.
 convert_time(&time,&timepoint);
 > FILETIME time: in system time format
 < timepoint.seconds, timepoint.minutes, timepoint.hours,
   timepoint.day, timepoint.month, timepoint.year. All as fixnums */
global void convert_time (const FILETIME* time, decoded_time_t* timepoint)
{
  var FILETIME ltime;
  var SYSTEMTIME ltm;
  if (!FileTimeToLocalFileTime(time,&ltime)) { OS_error(); }
  if (!FileTimeToSystemTime(&ltime,&ltm)) { OS_error(); }
  timepoint->seconds = fixnum(ltm.wSecond);
  timepoint->minutes = fixnum(ltm.wMinute);
  timepoint->hours   = fixnum(ltm.wHour);
  timepoint->day     = fixnum(ltm.wDay);
  timepoint->month   = fixnum(ltm.wMonth);
  timepoint->year    = fixnum(ltm.wYear);
}
#endif

#ifdef TIME_RELATIVE
/* Converts a decoded time to universal time.
 encode_universal_time(&timepoint)
 > decoded_time_t timepoint: decoded time
 < result: universal time
 can trigger GC */
local maygc object encode_universal_time (const decoded_time_t* timepoint)
{ /* (ENCODE-UNIVERSAL-TIME seconds minutes hours day month year): */
  pushSTACK(timepoint->seconds);
  pushSTACK(timepoint->minutes);
  pushSTACK(timepoint->hours);
  pushSTACK(timepoint->day);
  pushSTACK(timepoint->month);
  pushSTACK(timepoint->year);
  funcall(S(encode_universal_time),6);
  return value1;
}
#endif

#ifdef UNIX
/* UP: convert the system time format into lisp universal time.
 convert_time_to_universal(&time)
 > time_t time: in system time format
 < result: integer denoting the seconds since 1900-01-01 00:00 GMT
 can trigger GC */
global maygc object convert_time_to_universal (const time_t* time)
{
  /* Since we get the timezone from the OS (sys::default-time-zone),
     we can assume that the OS's timezone and CLISP's timezone agree. */
  return UL_to_I(UNIX_LISP_TIME_DIFF + (uintL)(*time));
}
/* the inverse of convert_time_to_universal() */
global void convert_time_from_universal (object universal, time_t* time)
{
  *time = I_to_UL(universal) - UNIX_LISP_TIME_DIFF;
}
#endif

#if defined(WIN32_NATIVE)
/* UP: convert the system (win32) time format into lisp universal time.
 convert_time_to_universal(&time)
 > FILETIME time: in system time format
 < result: integer denoting the seconds since 1900-01-01 00:00 GMT
 can trigger GC */
global maygc object convert_time_to_universal (const FILETIME* time) {
  /* Since we get the timezone from the OS (sys::defaul-time-zone),
     we can assume that the OS's timezone and CLISP's timezone agree. */
  var internal_time_t offset = /* difference between 1.1.1601 and 1.1.1900 */
   #ifdef HAVE_LONG_LONG_INT
    { (ULONG)((ULONGLONG)109207 * (ULONGLONG)86400
              * (ULONGLONG)ticks_per_second),
      (ULONG)(((ULONGLONG)109207 * (ULONGLONG)86400
               * (ULONGLONG)ticks_per_second) >> 32) };
   #else
    { 0xFDE04000, 0x14F373B };
   #endif
  var internal_time_t internal_real_time;
  var uintL real_time;
  sub_internal_time(*time,offset,internal_real_time);
  divu_6432_3232(internal_real_time.dwHighDateTime,
                 internal_real_time.dwLowDateTime,
                 ticks_per_second,
                 real_time=,);
  return UL_to_I(real_time);
}
/* the inverse of convert_time_to_universal() */
global void convert_time_from_universal (object universal, FILETIME* time) {
  var uint64 ut = (I_to_UQ(universal) + (uint64)109207 * (uint64)86400)
                  * (uint64)ticks_per_second;
  time->dwHighDateTime = (uint32)(ut>>32 & 0xFFFFFFFFul);
  time->dwLowDateTime =  (uint32)(ut     & 0xFFFFFFFFul);
}
#endif

/* ------------------------------------------------------------------------
 *                        Measuring wall clock time

 Wall clock time is measured with second resolution only.

Returns the wall clock time in seconds (since session start or 1900-01-01).*/
local uintL real_time_sec (void)
{
 #if TIME_METHOD == 1
  var uintL real_time = get_real_time();
  /* real_time := floor(real_time,ticks_per_second) : */
  #if (ticks_per_second == 1000000UL)
  divu_3216_3216(real_time>>6,ticks_per_second>>6,real_time=,);
  #elif (ticks_per_second < bit(16))
  divu_3216_3216(real_time,ticks_per_second,real_time=,);
  #else
  divu_3232_3232(real_time,ticks_per_second,real_time=,);
  #endif
 #elif TIME_METHOD == 2
  #ifdef TIME_UNIX
  var uintL real_time;     /* seconds */
  var internal_time_t it;
  get_real_time(&it);
  real_time = UNIX_LISP_TIME_DIFF + it.tv_sec;
  #endif
  #ifdef TIME_WIN32
  var internal_time_t offset = /* difference between 1.1.1601 and 1.1.1900 */
   #ifdef HAVE_LONG_LONG_INT
    { (ULONG)((ULONGLONG)109207 *
              (ULONGLONG)86400 * (ULONGLONG)ticks_per_second),
      (ULONG)(((ULONGLONG)109207 *
               (ULONGLONG)86400 * (ULONGLONG)ticks_per_second) >> 32)};
   #else
    { 0xFDE04000, 0x14F373B };
   #endif
  var internal_time_t internal_real_time;
  var uintL real_time;
  get_real_time(&internal_real_time);
  sub_internal_time(internal_real_time,offset,internal_real_time);
  divu_6432_3232(internal_real_time.dwHighDateTime,
                 internal_real_time.dwLowDateTime,
                 ticks_per_second,
                 real_time=,);
  #endif
 #endif
  return real_time;
}

#ifdef TIME_RELATIVE

/* Time and date at the LISP session start: */
local decoded_time_t realstart_datetime;

/* Sets the time of the start of the session.
 set_start_time(&timepoint);
 > timepoint: time at LISP session start
 >   timepoint.seconds in {0,...,59},
 >   timepoint.minutes in {0,...,59},
 >   timepoint.hours in {0,...,23},
 >   timepoint.day in {1,...,31},
 >   timepoint.month in {1,...,12},
 >   timepoint.year in {1980,...,2999},
 >   jeweils als Fixnums.
 can trigger GC */
local maygc void set_start_time (const decoded_time_t* timepoint)
{ /* save start time: */
  realstart_datetime = *timepoint;
  /* and, if possible, convert to universal time: */
  if (boundp(Symbol_function(S(encode_universal_time)))) {
    /* If ENCODE-UNIVERSAL-TIME is defined -> convert immediately into UT: */
    O(start_UT) = encode_universal_time(timepoint);
  }
}

/* Returns the time of the start of the session.
 get_start_time()
 can trigger GC */
local maygc uintL get_start_time (void)
{
  var object start_time = O(start_UT);
  if (nullp(start_time)) {  /* Start-Universal-Time still NIL ? */
    /* no -> already calculated.
       yes -> calculated anew: */
    start_time = O(start_UT) = encode_universal_time(&realstart_datetime);
  }
  return I_to_UL(start_time);
}

#endif

/* Returns the wall clock time in seconds (since 1900-01-01).
 can trigger GC */
local maygc uintL universal_time_sec (void);
#ifdef TIME_RELATIVE
local maygc uintL universal_time_sec()
{ return get_start_time() + real_time_sec(); }
#endif
#ifdef TIME_ABSOLUTE
#define universal_time_sec() real_time_sec()
#endif

LISPFUNNR(get_universal_time,0)
{ /* (get-universal-time), CLTL p. 445 */
  VALUES1(UL_to_I(universal_time_sec()));
}

/* UP: Initialises the time variables at the LISP session start.
 init_time(); */
global void init_time (void)
{ /* No gc happened -> no time to be added.
     gc_count=0;
     gc_time=0;
     gc_space=0; */
 #ifdef TIME_RELATIVE
  realstart_time = get_time(); /* Current time counter, now at the session start */
 #endif
 #ifndef HAVE_RUN_TIME
  /* run_time = 0; -- no run-time used, */
  run_flag = false;         /* because system is not yet running. */
  run_time_restart();       /* start run-time stopwatch */
 #endif
 #if defined(TIME_UNIX) || defined(TIME_WIN32)
  get_real_time(&realstart_time); /* Current time counter, now at the session start */
 #endif
 #ifdef TIME_RELATIVE
  { /* Get start time and save: */
    var decoded_time_t timepoint;
   #ifdef UNIX /* TIME_UNIX_TIMES */
    {
      var time_t real_time;
      begin_system_call();
      time(&real_time);     /* current time */
      end_system_call();
      convert_time(&real_time,&timepoint); /* convert to Decoded-Time */
    }
   #endif
    set_start_time(&timepoint); /* save start time */
  }
 #endif
}

/* ------------------------------------------------------------------------
 *                        Other time related functions */

#if defined(UNIX) || defined(WIN32)
local sintL seconds_west (time_t *now, int *isdst) {
  /* localtime() and gmtime() may return the same location,
     so we have to copy the rerned structure contents: */
  var struct tm now_local;
  var struct tm now_gm;
  begin_system_call();
  now_local = *(localtime(now));
  now_gm = *(gmtime(now));
  end_system_call();
  /* note that secondswest is NOT the same as
          mktime(&now_gm) - mktime(&now_local);
     during DST */
  var sintL dayswest = /* day difference = 0,1,-1 */
    (now_gm.tm_year < now_local.tm_year ? -1 :
     now_gm.tm_year > now_local.tm_year ? 1 :
     (now_gm.tm_mon < now_local.tm_mon ? -1 :
      now_gm.tm_mon > now_local.tm_mon ? 1 :
      (now_gm.tm_mday < now_local.tm_mday ? -1 :
       now_gm.tm_mday > now_local.tm_mday ? 1 :
       0)));
  var sintL hourswest = 24*dayswest
    + (sintL)(now_gm.tm_hour - now_local.tm_hour);
  var sintL minuteswest = 60*hourswest
    + (sintL)(now_gm.tm_min - now_local.tm_min);
  var sintL secondswest = 60*minuteswest
    + (sintL)(now_gm.tm_sec - now_local.tm_sec);
  *isdst = now_local.tm_isdst;
  return secondswest;
}

LISPFUNNR(default_time_zone,2)
{ /* (sys::default-time-zone hours ut-p) return TZ and DST-P for the
 given time in HOURS since the epoch; UT-P specifies whether HOURS is in
 Universal or Local time, i.e., the time that has elapsed since
 1900-01-01 0:0:0 GMT or since 1900-01-01 0:0:0 Local Time
 TZ takes into account DST-P, i.e., it is just the wall clock
 difference between local time and the UT
 The only access to TZ is localtime() and gmtime():
   TZ = (gmtime(t) - localtime(t))/3600.
   DST-P = localtime(t)->tm_isdst. */
  var bool ut_p = !nullp(popSTACK());
  var object arg = check_integer(popSTACK());
  var time_t now;
 #ifdef WIN32
  const uintL time_max = 1210107; /* Win32 crashes for greater values */
 #else
  const uintL time_max = 1314888; /* 1.1.2050, quite arbitrary */
 #endif
  if (posfixnump(arg)
      && (posfixnum_to_V(arg) >= 613608)   /* arg >= 1.1.1970 */
      && (posfixnum_to_V(arg) <= time_max)) { /* arg < time_max */
    now = (time_t)(posfixnum_to_V(arg) - 613608) * 3600;
  } else if (R_minusp(arg)
             || (posfixnump(arg) && (posfixnum_to_V(arg) < 613608))) {
    now = 0;                /* < 1.1.1970 -> treat like 1.1.1970 */
  } else {
    now = (time_t)(time_max - 613608) * 3600; /* > max -> treat like max */
  }
  var int isdst;
  var sintL secondswest = seconds_west(&now,&isdst);
  if (!ut_p) { /* convert now to UT and recompute isdst */
    now += secondswest;
    secondswest = seconds_west(&now,&isdst);
  }
  /* TZ in hours = (TZ in seconds / 3600) : */
  pushSTACK(L_to_I(secondswest));
  pushSTACK(fixnum(3600));
  funcall(L(slash),2);
  /* tm_isdst < 0 = "unknown"; assume no DST */
  VALUES2(value1, isdst > 0 ? T : NIL);
}
#endif  /* UNIX || WIN32 */

#ifdef TIME_UNIX_TIMES
/* Very bad replacement for the gettimeofday Function.
 Only to be used for time differences! */
local int gettimeofday (struct timeval * tp, void* tzp)
{
  if (!(tp==NULL)) {
    var uintL realtime = get_real_time();
    /* convert to seconds and microseconds: */
    tp->tv_sec = floor(realtime,ticks_per_second);
    tp->tv_usec = (realtime % ticks_per_second)
      * floor(2*1000000+ticks_per_second,2*ticks_per_second);
  }
  return 0;
}
#endif
LISPFUNN(sleep,2)
#if defined(TIME_UNIX) || defined(TIME_UNIX_TIMES)
{ /* (SYSTEM::%SLEEP delay-seconds delay-useconds) waits
 delay-seconds and delay-useconds microseconds.
 Argument delay-seconds must be a fixnum >=0, <=16700000,
 Argument delay-useconds must be a fixnum >=0, <=1000000. */
  var uintL useconds = posfixnum_to_V(popSTACK());
  var uintL seconds = posfixnum_to_V(popSTACK());
  begin_system_call();
  while (1) {
    var struct timeval start_time;
    var struct timeval end_time;
    if (!( gettimeofday(&start_time,NULL) ==0)) { OS_error(); }
   #ifdef HAVE_SELECT
    { /* select erlaubt eine wunderschöne Implementation von usleep(): */
      var struct timeval timeout; /* Zeitintervall */
      timeout.tv_sec = seconds; timeout.tv_usec = useconds;
      var int result;
      result = select(FD_SETSIZE,NULL,NULL,NULL,&timeout);
      if ((result<0) && !(errno==EINTR)) { OS_error(); }
    }
   #else
    if (seconds>0) { sleep(seconds); }
    #ifdef HAVE_USLEEP
    if (useconds>0) { usleep(useconds); }
    #endif
   #endif
    interruptp({
      end_system_call();
      pushSTACK(S(sleep)); tast_break(); /* evtl. Break-Schleife aufrufen */
      begin_system_call();
    });
    if (!( gettimeofday(&end_time,NULL) ==0)) { OS_error(); }
    /* Überprüfen, ob wir genügend lang geschlafen haben, oder ob
       wir wegen eines Signals zu früh aufgeweckt wurden: */
    var struct timeval slept; /* so lang haben wir geschlafen */
    /* sozusagen sub_internal_time(end_time,start_time, slept); */
    slept.tv_sec = end_time.tv_sec - start_time.tv_sec;
    if (end_time.tv_usec < start_time.tv_usec) {
      end_time.tv_usec += 1000000; slept.tv_sec -= 1;
    }
    slept.tv_usec = end_time.tv_usec - start_time.tv_usec;
    /* Haben wir genug geschlafen? */
    if ((slept.tv_sec > seconds)
        || ((slept.tv_sec == seconds) && (slept.tv_usec >= useconds)))
      break;
    /* Wie lange müssen wir noch schlafen? */
    seconds -= slept.tv_sec;
    if (useconds < slept.tv_usec) { seconds -= 1; useconds += 1000000; }
    useconds -= slept.tv_usec;
   #if !defined(HAVE_SELECT) && !defined(HAVE_USLEEP)
    if (seconds==0) break; /* CPU-Zeit fressende Warteschleife vermeiden */
   #endif
  }
  end_system_call();
  VALUES1(NIL);
}
#endif
#ifdef TIME_WIN32
{ /* (SYSTEM::%SLEEP delay-seconds delay-mseconds) waits
 delay-seconds und delay-mseconds milliseconds.
 Argument delay-seconds must be a fixnum >=0, <=4290000
 Argument delay-useconds must be a fixnum >=0, <=1000. */
  var uintL mseconds = posfixnum_to_V(popSTACK());
  var uintL seconds = posfixnum_to_V(popSTACK());
  begin_system_call();
  if (!msleep(1000*seconds+mseconds)) {
    end_system_call();
    pushSTACK(S(sleep)); tast_break(); /* evtl. call the break loop */
  } else {
    end_system_call();
  }
  VALUES1(NIL);
}
#endif

LISPFUNNR(time,0)
{ /* (SYSTEM::%%TIME) returns the time/space resource usage,
     without allocating space by itself and thereby causing a GC.
 9 values:
   Real-Time (system time since system start) in 2 values,
   Run-Time (used lisp time since system start) in 2 values,
   GC-Time (time in GC since system start) in 2 values,
   #ifdef TIME_UNIX_TIMES
     in CLK_TCK-stel seconds,
     (ldb (byte 16 16) time) and (ldb (byte 16 0) time).
   #endif
   #ifdef TIME_UNIX
     in microseconds,
     in whole seconds and microseconds.
   #endif
   #ifdef TIME_WIN32
     in tenth microseconds,
     in whole seconds and tenth microseconds.
   #endif
   Space (used since system start, in bytes)
     in 2 values: (ldb (byte 24 24) Space), (ldb (byte 24 0) Space).
   GC-Count (number of garbage collections in this session so far). */
  var timescore_t tm;
  get_running_times(&tm);     /* get run-time */
 #if TIME_METHOD == 1
  #define as_2_values(time)                \
    pushSTACK(fixnum(high16(time)));       \
    pushSTACK(fixnum(low16(time)));
 #elif TIME_METHOD == 2
  #ifdef TIME_UNIX
   #define as_2_values(time)                 \
     pushSTACK(fixnum(time.tv_sec));         \
     pushSTACK(fixnum(time.tv_usec));
  #endif
  #ifdef TIME_WIN32
    #define as_2_values(time)               \
      { var uintL tv_sec;                       \
        var uintL tv_usec;                                              \
        divu_6432_3232(time.dwHighDateTime,time.dwLowDateTime,ticks_per_second, tv_sec=, tv_usec=); \
        pushSTACK(fixnum(tv_sec));                                      \
        pushSTACK(fixnum(tv_usec));                                     \
      }
  #endif
 #endif                     /* TIME_METHOD */
  as_2_values(tm.realtime);   /* first two values: Real-Time */
  as_2_values(tm.runtime);    /* next two values: Run-Time */
  as_2_values(tm.gctime);     /* next two values: GC-Time */
  /* next two values: Space
     tm.gcfreed = freed space by the GC */
  {
    var uintM used = used_space(); /* currently used space */
    /* add both: */
   #ifdef intQsize
    tm.gcfreed += used;
   #else
    if ((tm.gcfreed.lo += used) < used) { tm.gcfreed.hi += 1; }
   #endif
  }
  /* Now tm.gcfreed = so far required space at all */
  #if (oint_data_len<24)
  #error "Fix function SYS::%%TIME!"
  #endif
  /* decode into 24 bits pieces: */
 #ifdef intQsize
  pushSTACK(fixnum( (tm.gcfreed>>24) & (bit(24)-1) ));
  pushSTACK(fixnum( tm.gcfreed & (bit(24)-1) ));
 #else
  pushSTACK(fixnum( ((tm.gcfreed.hi << 8) + (tm.gcfreed.lo >> 24)) & (bit(24)-1) ));
  pushSTACK(fixnum( tm.gcfreed.lo & (bit(24)-1) ));
 #endif
  /* last value: GC count */
  pushSTACK(fixnum(tm.gccount));
  funcall(L(values),9);       /* return 9 values */
}

/* (SYS::DELTA4 n1 n2 o1 o2 shift)
 compute the difference between [n1 n2] and [o1 o2]
 as positional numbers with SHIFT digits, i.e.,
 (- (+ (ash n1 shift) n2) (+ (ash o1 shift) o2))
 the difference must be positive
 all numbers must be fixnums < 2^32; the result is (UNSIGNED-BYTE 64) */
LISPFUNNF(delta4,5) {
  if (!posfixnump(STACK_0)) error_posfixnum(STACK_0);
  var uintV shift = posfixnum_to_V(STACK_0);
  if (!posfixnump(STACK_1)) error_posfixnum(STACK_1);
  var uintV o2 = posfixnum_to_V(STACK_1);
  if (!posfixnump(STACK_2)) error_posfixnum(STACK_2);
  var uintV o1 = posfixnum_to_V(STACK_2);
  if (!posfixnump(STACK_3)) error_posfixnum(STACK_3);
  var uintV n2 = posfixnum_to_V(STACK_3);
  if (!posfixnump(STACK_4)) error_posfixnum(STACK_4);
  var uintV n1 = posfixnum_to_V(STACK_4);
  if ((o1 > n1) || ((o1 == n1) && (o2 > n2))) {
    pushSTACK(STACK_3);     /* n2 */
    pushSTACK(STACK_(4+1)); /* n1 */
    pushSTACK(STACK_(1+2)); /* o2 */
    pushSTACK(STACK_(2+3)); /* o1 */
    pushSTACK(S(delta4));
    error(arithmetic_error,"~S: negative difference: [~S ~S] > [~S ~S]");
  }
  var uintV del = n1 - o1;
  if (shift >= 32 || shift + I_integer_length(fixnum(del)) > 64) {
    pushSTACK(STACK_0); pushSTACK(S(ash));
    error(arithmetic_error,GETTEXT("~S: too large shift amount ~S"));
  }
 #ifdef intQsize
  VALUES1(UQ_to_I(((uintQ)del << shift) + n2 - o2));
 #else
  var uint32 hi = del >> (32-shift);
  var uint32 lo = del << shift;
  if ((lo += n2) < n2) hi++;
  if (lo < o2) hi--; lo -= o2;
  VALUES1(UL2_to_I(hi, lo));
 #endif
  skipSTACK(5);
}
