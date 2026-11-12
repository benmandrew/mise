// What both fuzzing harnesses need from Lean, and how they report a failure.
//
// A harness links the Lean C of its module's import closure (see
// fuzz/build.sh) and calls the functions that module exports with
// `@[export]`. Each takes a ByteArray and returns a String, both owned: the
// callee consumes its arguments and the caller frees the result.

#ifndef MISE_FUZZ_LEAN_GLUE_H_
#define MISE_FUZZ_LEAN_GLUE_H_

#include <lean/lean.h>

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>

// Lean's C flags hide symbols by default, and on macOS libFuzzer finds
// LLVMFuzzerInitialize with dlsym, so the entry points are exported.
#define MISE_FUZZ_EXPORT extern "C" __attribute__((visibility("default")))

// Start the Lean runtime as the `main` that Lean generates for an
// executable does: the module's initialiser (`initialize_mise_<Module>`)
// starts the runtime itself and then initialises every module it imports.
inline void mise_lean_start(lean_object* (*initialize)(uint8_t builtin)) {
  static bool started = false;
  if (started) return;
  started = true;
  lean_object* res = initialize(1);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    abort();
  }
  lean_dec_ref(res);
  lean_init_task_manager();
}

// A new Lean ByteArray holding a copy of the bytes.
inline lean_object* mise_lean_bytes(const uint8_t* data, size_t size) {
  lean_object* arr = lean_alloc_sarray(1, size, size);
  if (size > 0) memcpy(lean_sarray_cptr(arr), data, size);
  return arr;
}

// The contents of a Lean String, which is freed.
inline std::string mise_lean_take_string(lean_object* s) {
  std::string out(lean_string_cstr(s), lean_string_size(s) - 1);
  lean_dec_ref(s);
  return out;
}

// Call an exported Lean function from ByteArray to String.
inline std::string mise_lean_call(lean_object* (*f)(lean_object*), const uint8_t* data, size_t size) {
  return mise_lean_take_string(f(mise_lean_bytes(data, size)));
}

// The number of failing inputs, or -1 when a failure should abort, as
// libFuzzer and AFL++ expect so that they keep the input. This weak
// definition is the default; fuzz/standalone.cc defines it as 0, so that
// the standalone engine counts failures and goes on.
extern "C" __attribute__((weak)) long mise_fuzz_failures = -1;

// Report that the current input failed, after the harness has printed why.
// Aborts, except under the standalone engine, where it returns and the
// harness returns from LLVMFuzzerTestOneInput.
inline void mise_fuzz_failed() {
  if (mise_fuzz_failures < 0) abort();
  mise_fuzz_failures++;
}

#endif  // MISE_FUZZ_LEAN_GLUE_H_
