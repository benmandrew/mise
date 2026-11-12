/* The command behind every edge of the random-graph harness (test/fuzz.py).

   fz MODE TAG OUT... -- IN...

   MODE holds `s` (static), `d` (depfile), `r` (restat) and `x` in any mix.
   The command reads its inputs in order. A depfile command also follows
   lines `include PATH` from what it reads, breadth first, skipping paths
   already read, and writes `OUT.d` for its first output. Output i gets the
   FNV-1a hash of the arguments after argv[0] joined by spaces, then i, then
   the contents of every file read with lines starting with `#` left out.
   A restat command leaves an output alone when its contents would not
   change. With `x` the command leaves out every output whose hash is a
   multiple of 3: it removes the file if it exists and writes nothing.
   Every run appends one line to `fz.log`:

     OUT T_START T_READ0 T_READ1 T_WRITE0 T_WRITE1 T_END READ...

   OUT is the first output, READ... the files read in order, and the times
   are CLOCK_MONOTONIC_RAW nanoseconds, which every process on the machine
   shares: at entry, before the first and after the last read of an input,
   before the first and after the last write (outputs and depfile; a
   `restat` command's look at its old output and an `x` command's removal
   count here), and before the log write. test/fuzz.py checks the schedule
   with them. When FZ_DELAY is set to N > 0, the command sleeps a random 0
   to N-1 microseconds after entry and again between reading and writing,
   so that parallel runs overlap more.

   When the environment variable FZ_FAIL names the first output, the
   command instead appends it to `fz.fail` and exits 1, before it reads or
   writes anything else. The harness uses this to stop a build part way.

   `fzContent` and `fzDyn` in test/MiseTest/Fuzz.lean compute the same
   contents and reads; the harness compares the two. */
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static unsigned long long now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC_RAW, &t);
  return (unsigned long long)t.tv_sec * 1000000000ULL + (unsigned long long)t.tv_nsec;
}

static void pause_random(long n) {
  if (n > 0) usleep((useconds_t)(random() % n));
}

static uint64_t feed(uint64_t h, const char *s, size_t n) {
  for (size_t i = 0; i < n; i++) {
    h ^= (unsigned char)s[i];
    h *= 1099511628211ULL;
  }
  return h;
}

static char *slurp(const char *path, size_t *len) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    *len = 0;
    return calloc(1, 1);
  }
  size_t cap = 4096, n = 0;
  char *buf = malloc(cap);
  size_t r;
  while ((r = fread(buf + n, 1, cap - n, f)) > 0) {
    n += r;
    if (n == cap) buf = realloc(buf, cap *= 2);
  }
  fclose(f);
  buf[n] = 0;
  *len = n;
  return buf;
}

static int appendLine(const char *path, const char *s) {
  int fd = open(path, O_WRONLY | O_APPEND | O_CREAT, 0644);
  if (fd < 0) return 0;
  size_t n = strlen(s);
  char *line = malloc(n + 1);
  memcpy(line, s, n);
  line[n] = '\n';
  int ok = write(fd, line, n + 1) == (ssize_t)(n + 1);
  free(line);
  return close(fd) == 0 && ok;
}

static int writeAll(const char *path, const char *s, size_t n) {
  FILE *f = fopen(path, "wb");
  if (!f || fwrite(s, 1, n, f) != n || fclose(f) != 0) {
    fprintf(stderr, "fz: cannot write %s\n", path);
    return 0;
  }
  return 1;
}

int main(int argc, char **argv) {
  unsigned long long t_start = now();
  const char *dv = getenv("FZ_DELAY");
  long delay = dv ? atol(dv) : 0;
  srandom((unsigned)(t_start ^ (unsigned long long)getpid() << 16));
  int sep = -1;
  for (int i = 3; i < argc; i++)
    if (strcmp(argv[i], "--") == 0) { sep = i; break; }
  if (argc < 4 || sep < 4) {
    fprintf(stderr, "usage: fz MODE TAG OUT... -- IN...\n");
    return 2;
  }
  const char *mode = argv[1];
  int dyn = strchr(mode, 'd') != NULL, restat = strchr(mode, 'r') != NULL, skip = strchr(mode, 'x') != NULL;
  int nouts = sep - 3;
  char **outs = argv + 3;
  const char *fail = getenv("FZ_FAIL");
  if (fail && strcmp(fail, outs[0]) == 0) {
    appendLine("fz.fail", outs[0]);
    return 1;
  }

  /* Files to read, in reading order. */
  int cap = 64, n = 0;
  char **reads = malloc(cap * sizeof *reads);
  for (int i = sep + 1; i < argc; i++) {
    int seen = 0;
    for (int j = 0; j < n; j++) seen |= strcmp(reads[j], argv[i]) == 0;
    if (!seen) reads[n++] = argv[i];
    if (n == cap) reads = realloc(reads, (cap *= 2) * sizeof *reads);
  }

  uint64_t key = 14695981039346656037ULL;
  for (int i = 1; i < argc; i++) {
    if (i > 1) key = feed(key, " ", 1);
    key = feed(key, argv[i], strlen(argv[i]));
  }
  key = feed(key, "\n", 1);

  char **texts = malloc(cap * sizeof *texts);
  size_t *lens = malloc(cap * sizeof *lens);
  pause_random(delay);
  unsigned long long t_read0 = now();
  for (int k = 0; k < n; k++) {
    texts[k] = slurp(reads[k], &lens[k]);
    if (!dyn) continue;
    char *s = texts[k], *end = s + lens[k];
    while (s <= end) {
      char *nl = memchr(s, '\n', end - s);
      char *e = nl ? nl : end;
      if (e - s > 8 && strncmp(s, "include ", 8) == 0) {
        size_t pl = e - s - 8;
        int seen = 0;
        for (int j = 0; j < n; j++) seen |= strlen(reads[j]) == pl && strncmp(reads[j], s + 8, pl) == 0;
        if (!seen) {
          if (n + 1 >= cap) {
            cap *= 2;
            reads = realloc(reads, cap * sizeof *reads);
            texts = realloc(texts, cap * sizeof *texts);
            lens = realloc(lens, cap * sizeof *lens);
          }
          reads[n++] = strndup(s + 8, pl);
        }
      }
      if (!nl) break;
      s = nl + 1;
    }
  }

  unsigned long long t_read1 = now();

  /* Hash before the write phase, so that it holds only file accesses. */
  char (*outv)[32] = malloc(nouts * sizeof *outv);
  int *outl = malloc(nouts * sizeof *outl);
  for (int i = 0; i < nouts; i++) {
    char idx[32];
    int il = snprintf(idx, sizeof idx, "%d\n", i);
    uint64_t h = feed(key, idx, il);
    for (int k = 0; k < n; k++) {
      char *s = texts[k], *end = s + lens[k];
      while (1) {
        char *nl = memchr(s, '\n', end - s);
        char *e = nl ? nl : end;
        if (!(e > s && *s == '#')) {
          h = feed(h, s, e - s);
          h = feed(h, "\n", 1);
        }
        if (!nl) break;
        s = nl + 1;
      }
      h = feed(h, "\0", 1);
    }
    /* -1 marks an output that an `x` command leaves out. */
    outl[i] = skip && h % 3 == 0 ? -1 : snprintf(outv[i], sizeof outv[i], "%016llx\n", (unsigned long long)h);
  }

  pause_random(delay);
  unsigned long long t_write0 = now();
  for (int i = 0; i < nouts; i++) {
    char *out = outv[i];
    int ol = outl[i];
    if (ol < 0) {
      unlink(outs[i]);
      continue;
    }
    if (restat) {
      size_t len;
      char *old = slurp(outs[i], &len);
      int same = len == (size_t)ol && memcmp(old, out, ol) == 0;
      free(old);
      if (same) continue;
    }
    if (!writeAll(outs[i], out, ol)) return 1;
  }

  if (dyn) {
    size_t dl = strlen(outs[0]) + 3;
    char *dpath = malloc(dl);
    snprintf(dpath, dl, "%s.d", outs[0]);
    FILE *f = fopen(dpath, "wb");
    if (!f) return 1;
    fprintf(f, "%s:", outs[0]);
    for (int k = 0; k < n; k++) fprintf(f, " %s", reads[k]);
    fprintf(f, "\n");
    fclose(f);
  }
  unsigned long long t_write1 = now();

  /* One write(2) per line, so that lines from parallel runs do not mix. */
  size_t ll = strlen(outs[0]) + 6 * 21 + 2;
  for (int k = 0; k < n; k++) ll += strlen(reads[k]) + 1;
  char *line = malloc(ll);
  int len = snprintf(line, ll, "%s %llu %llu %llu %llu %llu %llu", outs[0], t_start, t_read0, t_read1, t_write0,
                     t_write1, now());
  for (int k = 0; k < n; k++) len += snprintf(line + len, ll - len, " %s", reads[k]);
  line[len++] = '\n';
  int log = open("fz.log", O_WRONLY | O_APPEND | O_CREAT, 0644);
  if (log < 0) return 1;
  if (write(log, line, len) != (ssize_t)len) return 1;
  close(log);
  return 0;
}
