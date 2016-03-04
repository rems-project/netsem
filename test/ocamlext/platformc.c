#ifdef WIN32
#include <winsock2.h>
#include <windows.h>
#include <process.h>
#include <sys/types.h>
#include <sys/timeb.h>
#include <fcntl.h>
#endif

#include "mlvalues.h"
#include "memory.h"

#include <alloc.h>
#include <memory.h>
#include <stdio.h>
#include <errno.h>
#include <time.h>
#include <string.h>

#ifndef WIN32
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/time.h>
#include <unistd.h>
#include <pthread.h>
#endif
#ifdef __sun
#define _POSIX_PTHREAD_SEMANTICS
#endif

#ifndef WIN32
#include "signals.h"
#endif
#include "unixsupport.h"

#ifdef __FreeBSD__
int c_platform=2;
#else
#ifdef bsd
int c_platform=2;
#else
#ifdef BSD
int c_platform=2;
#else
#ifdef linux
#define LINUX
int c_platform=1;
#else
#ifdef unix
int c_platform=1;
#else
#ifdef WIN32
int c_platform=0;
#else
int c_platform=3;
#endif
#endif
#endif
#endif
#endif
#endif


CAMLprim value c_check_platform()
{
  return Val_int(c_platform);
}

CAMLprim value c_gethostname()
{
  char name[50];

  if(gethostname(name, 50) == -1) {
   perror("c_gethostname() failed");
   abort();
  }

  return copy_string(name);
}

#ifndef WIN32
CAMLprim value c_gettimeofday()
{
  time_t currtime;
  char *timestr;

  time(&currtime);
  timestr = ctime(&currtime);
  timestr[strlen(timestr)-1] = '\0';

  return copy_string(timestr);
}
#else
CAMLprim value c_gettimeofday()
{
  struct __timeb64 timebuffer;
  char *timestr;

  _ftime64(&timebuffer);
  timestr = _ctime64(&(timebuffer.time));

  return copy_string(timestr);
}
#endif

#ifndef WIN32
CAMLprim value c_getdecenttimeofday()
{
  struct timeval currtime;
  struct timezone tz;
  value t = Val_unit;

  gettimeofday(&currtime, &tz);

  Begin_root(t);
  t = alloc_small(2, 0);
  Field(t, 0) = Val_long(currtime.tv_sec);
  Field(t, 1) = Val_long(currtime.tv_usec);
  End_roots();

  return t;
}
#else
CAMLprim value c_getdecenttimeofday()
{
  struct _timeb timebuffer;
  value t = Val_unit;

  _ftime( &timebuffer );

  Begin_root(t);
  t = alloc_small(2, 0);
  Field(t, 0) = Val_long(timebuffer.time);
  Field(t, 1) = Val_long(timebuffer.millitm * 1000);
  End_roots();

  return t;
}
#endif


#ifdef LINUX
CAMLprim value getpty()
{
  value result = Val_unit;
  int master, slave;

  master = getpt();
  slave = open(ptsname(master),  O_NOCTTY);

  Begin_root(result);
  result = alloc_small(2, 0);
  Field(result, 0) = Val_int(master);
  Field(result, 1) = Val_int(slave);
  End_roots();
  return result;
}
#else
CAMLprim value getpty()
{
  fprintf(stderr, "getpty() failed\n");
  abort();

  return Val_unit;
}
#endif



#ifndef WIN32
/* defines stolen from OCaml's posix.c */
#define Condition_val(v) (* ((pthread_cond_t **) Data_custom_val(v)))
#define Mutex_val(v) (* ((pthread_mutex_t **) Data_custom_val(v)))
#else
/* defines stolen from Ocaml's win32.c (slightly modified to avoid namespace clash */
struct caml_condvar {
    unsigned long count;
    HANDLE sem;
};

#define Condition_val_win32(v) ((struct caml_condvar *) Data_custom_val(v))
#define Mutex_val_win32(v) (*((HANDLE *) Data_custom_val(v)))
#endif

#ifndef WIN32
value c_condition_abs_timedwait(value wcond, value wmut, value wabstime)
{
  int retcode;
  struct timespec tv;
  struct timespec * tvp;

  pthread_cond_t * cond = Condition_val(wcond);
  pthread_mutex_t * mut = Mutex_val(wmut);
  double tm = Double_val(wabstime);

  Begin_roots2(wcond, wmut)     /* prevent deallocation of cond and mutex */
    if (tm < 0.0)
      tvp = (struct timespec *) NULL;
    else {
      tv.tv_sec = (int) tm;
      tv.tv_nsec = (int) (1e9 * (tm - tv.tv_sec));
      tvp = &tv;
    }
    enter_blocking_section();
    retcode = pthread_cond_timedwait(cond, mut, tvp);
    leave_blocking_section();
  End_roots();
  if (retcode != 0) unix_error(retcode, "condition_abs_timedwait", Nothing);
  return Val_unit;
}
#else
value c_condition_abs_timedwait(value wcond, value wmut, value wabstime)
{
  int retcode;
  HANDLE m = Mutex_val_win32(wmut);
  HANDLE s = Condition_val_win32(wcond)->sem;
  HANDLE handles[2];
  struct _timeb timebuffer;
  double tm = Double_val(wabstime);
  int secs = (int) tm;
  int milli = (int) (1e3 * (tm - secs));
  int millis = 0;

  _ftime(&timebuffer);

  millis = (timebuffer.time*1000 + timebuffer.millitm) -
      (secs*1000 + milli);
  if(millis < 0) millis = 0;
  if(tm < 0.0) millis = 0;

  Condition_val_win32(wcond)->count ++;
  Begin_roots2(wcond, wmut) /* Prevent deallocation */
    enter_blocking_section();
    /* Release mutex */
    ReleaseMutex(m);
    /* Wait for semaphore to be non-null, and decrement it.
       Simultaneously, reaquire mutex. */
    handles[0] = s;
    handles[1] = m;
    retcode = WaitForMultipleObjects(2, handles, TRUE, millis);
    leave_blocking_section();
  End_roots();

  if(retcode == WAIT_FAILED) uerror("Condition.abs_timedwait", Nothing);
  return Val_unit;
}
#endif


#ifndef WIN32
value c_condition_rel_timedwait(value wcond, value wmut, value wreltime)
{
  int retcode;
  struct timeval now;
  struct timespec tv;
  struct timespec * tvp;

  pthread_cond_t * cond = Condition_val(wcond);
  pthread_mutex_t * mut = Mutex_val(wmut);
  double tm = Double_val(wreltime);

  Begin_roots2(wcond, wmut)     /* prevent deallocation of cond and mutex */
    if (tm < 0.0)
      tvp = (struct timespec *) NULL;
    else {
      gettimeofday(&now,NULL);
      tv.tv_sec = now.tv_sec + (int) tm;
      tv.tv_nsec = now.tv_usec * 1000 + (int) (1e9 * (tm - (int) tm));
      // does nsec total more than 1 sec?
      if (tv.tv_nsec >= 1e9) {
	tv.tv_sec = tv.tv_sec + 1;
	tv.tv_nsec = tv.tv_nsec - 1e9;
      }
      tvp = &tv;
    }
    enter_blocking_section();
    retcode = pthread_cond_timedwait(cond, mut, tvp);
    leave_blocking_section();
  End_roots();
  if (retcode != 0) {
    //retcode = errno;
    if (retcode == EINTR) {
      gettimeofday(&now,NULL);
      if (now.tv_sec > tv.tv_sec || (now.tv_sec == tv.tv_sec && now.tv_usec >= tv.tv_nsec / 1000)) {
        /* work around Linux bug: EINTR returned instead of ETIMEDOUT */
        retcode = ETIMEDOUT;
      }
    }
    unix_error(retcode, "condition_rel_timedwait", Nothing);
  }
  return Val_unit;
}
#else
value c_condition_rel_timedwait(value wcond, value wmut, value wreltime)
{
   int retcode;
  HANDLE m = Mutex_val_win32(wmut);
  HANDLE s = Condition_val_win32(wcond)->sem;
  HANDLE handles[2];
  double tm = Double_val(wreltime);
  int secs = (int) tm;
  int milli = (int) (1e3 * (tm - secs));
  int millis = secs*1000 + milli;

  if(tm < 0.0) millis = 0;

  Condition_val_win32(wcond)->count ++;
  Begin_roots2(wcond, wmut) /* Prevent deallocation */
    enter_blocking_section();
    /* Release mutex */
    ReleaseMutex(m);
    /* Wait for semaphore to be non-null, and decrement it.
      Simultaneously, reaquire mutex. */
    handles[0] = s;
    handles[1] = m;
    retcode = WaitForMultipleObjects(2, handles, TRUE, millis);
    leave_blocking_section();
  End_roots();

  if(retcode == WAIT_FAILED) uerror("Condition.abs_timedwait", Nothing);
  return Val_unit;
}
#endif


#ifdef WIN32
CAMLprim value c_win32_terminate_process(value vpid_req, value code)
{
  DWORD errcode;
  char buff[50];

  HANDLE pid_req = (HANDLE) Long_val(vpid_req);
  int exitcode = Int_val(code);

  if(!TerminateProcess(pid_req, exitcode)) {
    errcode = GetLastError();
    sprintf(buff, "win32_terminate_process failed: %d", errcode);
    uerror("win32_terminate_process failed", Nothing);
    return Val_unit;
  }

  return Val_unit;
}
#else
CAMLprim value c_win32_terminate_process(value pid, value code)
{
  uerror("win32_terminate_process not implemented on non-Win32 platforms", Nothing);
  return Val_unit;
}
#endif


#ifdef WIN32
struct filedescr {
  union {
     HANDLE handle;
     SOCKET socket;
  } fd;
  enum { KIND_HANDLE, KIND_SOCKET } kind;
};

#define Handle_val(v) (((struct filedescr *) Data_custom_val(v))->fd.socket)

CAMLprim value c_win32_open_handle(value handle)
{
  int fd;
  fprintf(stderr, "IN c_win32_open_handle\n\n");
  fd = _open_osfhandle((long) Handle_val(handle), 0);
  if (fd == -1) {
    perror("FAILED WITH");
    uerror("c_win32_open_handle failed!!!", Nothing);
  }
  fprintf(stderr, "LEAVING c_win32_open_handle\n\n");
  return Val_int(fd);
}
#else
CAMLprim value c_win32_open_handle(value handle)
{
  uerror("c_win32_open_handle NOT IMPLEMENTED on non-WIN32 platforms", Nothing);
  return Val_int(-1);
}
#endif

#ifdef WIN32
CAMLprim value c_win32_free_open_handle(value handle)
{
    _free_osfhnd(Int_val(handle));
    return Val_unit;
}
#else
CAMLprim value c_win32_free_open_handle(value handle)
{
  uerror("c_win32_free_open_handle NOT IMPLEMENTED on non-WIN32 platforms", Nothing);
  return Val_int(-1);
}
#endif
