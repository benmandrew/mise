/* The command behind every edge of the random-graph harness (test/fuzz.py).

   fz MODE TAG OUT... -- IN...

   MODE holds `s` (static), `d` (depfile) and `r` (restat) in any mix.
   The command reads its inputs in order. A depfile command also follows
   lines `include PATH` from what it reads, breadth first, skipping paths
   already read, and writes `OUT.d` for its first output. Output i gets the
   FNV-1a hash of the arguments after argv[0] joined by spaces, then i, then
   the contents of every file read with lines starting with `#` left out.
   A restat command leaves an output alone when its contents would not
   change. Every run appends its first output to `fz.log`.

   `fzContent` and `fzDyn` in test/MiseTest/Fuzz.lean compute the same
   contents and reads; the harness compares the two. */
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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

static int writeAll(const char *path, const char *s, size_t n) {
  FILE *f = fopen(path, "wb");
  if (!f || fwrite(s, 1, n, f) != n || fclose(f) != 0) {
    fprintf(stderr, "fz: cannot write %s\n", path);
    return 0;
  }
  return 1;
}

int main(int argc, char **argv) {
  int sep = -1;
  for (int i = 3; i < argc; i++)
    if (strcmp(argv[i], "--") == 0) { sep = i; break; }
  if (argc < 4 || sep < 4) {
    fprintf(stderr, "usage: fz MODE TAG OUT... -- IN...\n");
    return 2;
  }
  const char *mode = argv[1];
  int dyn = strchr(mode, 'd') != NULL, restat = strchr(mode, 'r') != NULL;
  int nouts = sep - 3;
  char **outs = argv + 3;

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
    char out[32];
    int ol = snprintf(out, sizeof out, "%016llx\n", (unsigned long long)h);
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

  int log = open("fz.log", O_WRONLY | O_APPEND | O_CREAT, 0644);
  if (log < 0) return 1;
  size_t ol = strlen(outs[0]);
  char *line = malloc(ol + 2);
  memcpy(line, outs[0], ol);
  line[ol] = '\n';
  if (write(log, line, ol + 1) != (ssize_t)(ol + 1)) return 1;
  close(log);
  return 0;
}
