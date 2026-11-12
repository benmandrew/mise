// The standalone engine: a main for a fuzzing harness without a fuzzer.
//
//   BIN FILE...          replay the inputs in the files
//   BIN [N [SEED [K]]]   run N inputs (default 100) of K pseudo-random
//                        bytes (default 4096), the i-th drawn from seed
//                        SEED + i (default 0), and print the rate
//
// It calls the harness's LLVMFuzzerInitialize and LLVMFuzzerTestOneInput,
// as libFuzzer does. A failing input does not abort: `mise_fuzz_failed`
// (fuzz/lean_glue.h) counts it, the run goes on, and the exit status is 1
// when any input failed. After the rate line it calls the harness's
// `mise_fuzz_stats`, when the harness defines one, to print its own
// statistics.
//
// This file does not include Lean or Ninja.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include <string>
#include <vector>

extern "C" int LLVMFuzzerInitialize(int* argc, char*** argv);
extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size);

// Overrides the weak default in fuzz/lean_glue.h: count failures.
extern "C" long mise_fuzz_failures = 0;

// The harness's statistics hook, given the wall time of the run. A weak
// definition rather than a weak reference, which Mach-O cannot leave
// undefined in a static link.
extern "C" __attribute__((weak)) void mise_fuzz_stats(double seconds) { (void)seconds; }

static uint64_t splitmix(uint64_t* s) {
  uint64_t z = (*s += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}

static double now() {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec / 1e9;
}

int main(int argc, char** argv) {
  LLVMFuzzerInitialize(&argc, &argv);
  double t0 = now();
  long n = 0;
  if (argc >= 2 && access(argv[1], F_OK) == 0) {
    for (int i = 1; i < argc; i++) {
      FILE* f = fopen(argv[i], "rb");
      if (!f) {
        fprintf(stderr, "standalone: cannot read %s\n", argv[i]);
        return 2;
      }
      std::string s;
      char buf[4096];
      size_t k;
      while ((k = fread(buf, 1, sizeof buf, f)) > 0) s.append(buf, k);
      fclose(f);
      long before = mise_fuzz_failures;
      LLVMFuzzerTestOneInput((const uint8_t*)s.data(), s.size());
      if (mise_fuzz_failures > before) fprintf(stderr, "standalone: %s fails\n", argv[i]);
      n++;
    }
  } else {
    n = argc >= 2 ? atol(argv[1]) : 100;
    uint64_t seed = argc >= 3 ? strtoull(argv[2], nullptr, 10) : 0;
    size_t bytes = argc >= 4 ? strtoul(argv[3], nullptr, 10) : 4096;
    std::vector<uint8_t> in(bytes);
    for (long i = 0; i < n; i++) {
      uint64_t x = seed + i;
      for (auto& b : in) b = (uint8_t)splitmix(&x);
      LLVMFuzzerTestOneInput(in.data(), in.size());
    }
  }
  double s = now() - t0;
  printf("%ld inputs in %.2f s: %.1f inputs/s; %ld failures\n", n, s, n / s, mise_fuzz_failures);
  mise_fuzz_stats(s);
  return mise_fuzz_failures ? 1 : 0;
}
