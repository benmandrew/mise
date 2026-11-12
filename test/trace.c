/* Record the files a command opens (test/confine.py, `trace` mode).

   Build as a shared library and load it into every process of a command:
     macOS: cc -dynamiclib -o libtrace.dylib test/trace.c
            DYLD_INSERT_LIBRARIES=libtrace.dylib MISE_TRACE=LOG cmd...
     Linux: cc -shared -fPIC -o libtrace.so test/trace.c -ldl
            LD_PRELOAD=libtrace.so MISE_TRACE=LOG cmd...

   After each successful open the library appends one line to LOG:
   `R PATH`, `W PATH` or `D PATH` (a file opened for reading only, a file
   opened for writing, a directory), with PATH the resolved absolute path
   of the open descriptor. An open refused with EPERM or EACCES (as under a
   sandbox profile) gives `E PATH`, with PATH as the caller passed it.
   It wraps `open`, `openat` and `fopen` and their
   variants; a process that reads files through other calls (`mmap` of a
   descriptor it got elsewhere, direct system calls, `posix_spawn` of a
   binary) is not seen. The Linux half is untested. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

/* The real calls. On macOS the interposing image's own calls are not
   interposed, so the names refer to libc; on Linux they come from
   dlsym(RTLD_NEXT). */
#ifdef __APPLE__
#define REAL(f) f
#else
#include <dlfcn.h>
#define REAL(f) real_##f()
#define DEF_REAL(ret, f, args)                                  \
  static ret(*real_##f(void)) args {                            \
    static ret(*p) args;                                        \
    if (!p) p = (ret(*) args)dlsym(RTLD_NEXT, #f);              \
    return p;                                                   \
  }
DEF_REAL(int, open, (const char *, int, ...))
DEF_REAL(int, open64, (const char *, int, ...))
DEF_REAL(int, openat, (int, const char *, int, ...))
DEF_REAL(int, openat64, (int, const char *, int, ...))
DEF_REAL(FILE *, fopen, (const char *, const char *))
DEF_REAL(FILE *, fopen64, (const char *, const char *))
#endif

/* The log path, read once at load time. `record` runs inside libc calls
   that hold locks (setlocale opens files), so it calls nothing that might
   take one: no getenv, no printf. */
static char log_path[PATH_MAX];

__attribute__((constructor)) static void init(void) {
  const char *p = getenv("MISE_TRACE");
  if (p && strlen(p) < sizeof log_path) strcpy(log_path, p);
}

static void record(int fd, int writing, const char *req) {
  if (!log_path[0]) return;
  int saved = errno;
  if (fd < 0 && saved != EPERM && saved != EACCES) return;
  char line[PATH_MAX + 4];
  char *path = line + 2;
  if (fd < 0) {
    if (strlen(req) >= PATH_MAX) goto out;
    strcpy(path, req);
    line[0] = 'E';
    goto write;
  }
#ifdef __APPLE__
  if (fcntl(fd, F_GETPATH, path) == -1) goto out;
#else
  char link[32] = "/proc/self/fd/";
  char digits[16];
  int nd = 0;
  for (unsigned v = (unsigned)fd; nd == 0 || v; v /= 10) digits[nd++] = (char)('0' + v % 10);
  for (int i = 0; i < nd; i++) link[14 + i] = digits[nd - 1 - i];
  link[14 + nd] = 0;
  ssize_t n = readlink(link, path, PATH_MAX - 1);
  if (n < 0) goto out;
  path[n] = 0;
#endif
  struct stat st;
  line[0] = writing ? 'W' : 'R';
  if (fstat(fd, &st) == 0 && S_ISDIR(st.st_mode)) line[0] = 'D';
write:
  line[1] = ' ';
  size_t len = 2 + strlen(path);
  line[len++] = '\n';
  int lfd = REAL(open)(log_path, O_WRONLY | O_APPEND | O_CREAT | O_CLOEXEC, 0644);
  if (lfd >= 0) {
    if (write(lfd, line, len) < 0) { /* nothing to do */ }
    close(lfd);
  }
out:
  errno = saved;
}

static int writes(int flags) { return (flags & O_ACCMODE) != O_RDONLY || (flags & (O_CREAT | O_TRUNC)); }

static int fwrites(const char *mode) { return strpbrk(mode, "wa+") != NULL; }

static mode_t mode_arg(int flags, va_list ap) {
#ifdef O_TMPFILE
  if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) return (mode_t)va_arg(ap, int);
#else
  if (flags & O_CREAT) return (mode_t)va_arg(ap, int);
#endif
  return 0;
}

#define WRAP_OPEN(name, real)                          \
  int name(const char *p, int flags, ...) {            \
    va_list ap;                                        \
    va_start(ap, flags);                               \
    mode_t m = mode_arg(flags, ap);                    \
    va_end(ap);                                        \
    int fd = real(p, flags, m);                        \
    record(fd, writes(flags), p);                         \
    return fd;                                         \
  }

#define WRAP_OPENAT(name, real)                        \
  int name(int dir, const char *p, int flags, ...) {   \
    va_list ap;                                        \
    va_start(ap, flags);                               \
    mode_t m = mode_arg(flags, ap);                    \
    va_end(ap);                                        \
    int fd = real(dir, p, flags, m);                   \
    record(fd, writes(flags), p);                         \
    return fd;                                         \
  }

#define WRAP_FOPEN(name, real)                         \
  FILE *name(const char *p, const char *mode) {        \
    FILE *f = real(p, mode);                           \
    record(f ? fileno(f) : -1, fwrites(mode), p);           \
    return f;                                          \
  }

#ifdef __APPLE__
/* dyld replaces every other image's references to the second symbol of a
   pair with the first. libc calls the `$NOCANCEL` variants internally. */
int open_nocancel(const char *, int, ...) __asm("_open$NOCANCEL");
int openat_nocancel(int, const char *, int, ...) __asm("_openat$NOCANCEL");

WRAP_OPEN(trace_open, open)
WRAP_OPEN(trace_open_nocancel, open_nocancel)
WRAP_OPENAT(trace_openat, openat)
WRAP_OPENAT(trace_openat_nocancel, openat_nocancel)
WRAP_FOPEN(trace_fopen, fopen)

#define INTERPOSE(a, b)                                                    \
  __attribute__((used)) static struct { const void *r, *o; } interpose_##b \
      __attribute__((section("__DATA,__interpose"))) = {(const void *)a, (const void *)b};
INTERPOSE(trace_open, open)
INTERPOSE(trace_open_nocancel, open_nocancel)
INTERPOSE(trace_openat, openat)
INTERPOSE(trace_openat_nocancel, openat_nocancel)
INTERPOSE(trace_fopen, fopen)
#else
WRAP_OPEN(open, real_open())
WRAP_OPEN(open64, real_open64())
WRAP_OPENAT(openat, real_openat())
WRAP_OPENAT(openat64, real_openat64())
WRAP_FOPEN(fopen, real_fopen())
WRAP_FOPEN(fopen64, real_fopen64())
#endif
