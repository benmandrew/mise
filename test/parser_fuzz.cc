// Differential parser fuzzer: Ninja's manifest parser against the Lean
// parser model (test/MiseTest/ParseFuzz.lean), in one process.
//
// Built and run by test/parser-fuzz.sh. MISE_FUZZ_MODE=text (the default)
// treats each input as manifest text. MISE_FUZZ_MODE=gen passes the input
// to the Lean manifest generator as its choice sequence and parses the text
// it prints, so every input is a manifest the model accepts.
//
// When the model accepts a manifest, Ninja must accept it too and read the
// same edges, edge variables and defaults; otherwise the harness prints both
// readings and aborts, which libFuzzer reports as a crash. An input the model
// rejects is not checked, since Ninja reads more than the model's subset.

#include <lean/lean.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <utility>
#include <vector>

#include "disk_interface.h"
#include "graph.h"
#include "manifest_parser.h"
#include "state.h"
#include "version.h"

extern "C" {
lean_object* initialize_mise_MiseTest_ParseFuzz(uint8_t builtin);
lean_object* mise_fuzz_text(lean_object* bytes);
lean_object* mise_fuzz_gen(lean_object* bytes);
}

namespace {

using Fields = std::vector<std::pair<std::string, std::string>>;

bool gen_mode = false;

// The edge variables the Lean side evaluates for every non-phony edge.
const char* const kKeys[] = {"command", "description", "depfile", "deps", "restat"};

// Call an exported Lean function on a byte array and return its string.
std::string call_lean(lean_object* (*f)(lean_object*), const uint8_t* data, size_t size) {
  lean_object* arr = lean_alloc_sarray(1, size, size);
  if (size > 0) memcpy(lean_sarray_cptr(arr), data, size);
  lean_object* res = f(arr);  // takes ownership of arr
  std::string out(lean_string_cstr(res), lean_string_size(res) - 1);
  lean_dec(res);
  return out;
}

void add(Fields* fs, const char* key, const std::string& value) { fs->emplace_back(key, value); }

// Read fields in the `KEY LEN:VALUE\n` format of `ParseFuzz.dump`.
Fields parse_fields(const std::string& s) {
  Fields fs;
  size_t i = 0;
  while (i < s.size()) {
    size_t sp = s.find(' ', i), colon = s.find(':', sp);
    if (sp == std::string::npos || colon == std::string::npos) abort();
    size_t len = std::stoul(s.substr(sp + 1, colon - sp - 1));
    fs.emplace_back(s.substr(i, sp - i), s.substr(colon + 1, len));
    i = colon + 1 + len + 1;
  }
  return fs;
}

// Ninja's reading of a manifest it accepted, in the same order as `dump`.
// `cyclic[i]` says whether the model found a cycle in edge i's rule
// variables; Ninja would exit on evaluating them, so they are left out, and
// when the edge counts differ every edge's variables are.
Fields ninja_fields(const State& state, const std::vector<bool>& cyclic) {
  Fields fs;
  bool same_count = state.edges_.size() == cyclic.size();
  for (size_t ei = 0; ei < state.edges_.size(); ++ei) {
    const Edge* e = state.edges_[ei];
    add(&fs, "edge", e->rule().name());
    size_t nout = e->outputs_.size() - e->implicit_outs_;
    for (size_t i = 0; i < e->outputs_.size(); ++i)
      add(&fs, i < nout ? "out" : "iout", e->outputs_[i]->path());
    size_t nin = e->inputs_.size() - e->implicit_deps_ - e->order_only_deps_;
    size_t nimp = nin + e->implicit_deps_;
    for (size_t i = 0; i < e->inputs_.size(); ++i)
      add(&fs, i < nin ? "in" : i < nimp ? "iin" : "oo", e->inputs_[i]->path());
    for (const Node* v : e->validations_) add(&fs, "validation", v->path());
    if (e->is_phony()) continue;
    if (!same_count || cyclic[ei]) add(&fs, "cyclic", "");
    else for (const char* k : kKeys) add(&fs, k, e->GetBinding(k));
  }
  for (const Node* d : state.defaults_) add(&fs, "default", d->path());
  return fs;
}

// Whether Ninja passes every version without a warning or a fatal error,
// which would print or exit instead of returning an error.
bool versions_quiet(const Fields& versions) {
  int bin_major, bin_minor;
  ParseVersion(kNinjaVersion, &bin_major, &bin_minor);
  for (const auto& v : versions) {
    int major, minor;
    ParseVersion(v.second, &major, &minor);
    if (major != bin_major || minor > bin_minor) return false;
  }
  return true;
}

std::string escape(const std::string& s) {
  std::string out;
  for (unsigned char c : s) {
    if (c == '\n') out += "\\n";
    else if (c == '\\') out += "\\\\";
    else if (c < 0x20 || c == 0x7f) { char b[8]; snprintf(b, sizeof b, "\\x%02x", c); out += b; }
    else out += static_cast<char>(c);
  }
  return out;
}

void print_fields(const char* who, const Fields& fs) {
  fprintf(stderr, "%s:\n", who);
  for (const auto& f : fs) fprintf(stderr, "  %s \"%s\"\n", f.first.c_str(), escape(f.second).c_str());
}

[[noreturn]] void fail(const std::string& text, const char* what, const Fields* model, const Fields* ninja) {
  fprintf(stderr, "\nmise parser fuzz: %s\nmanifest:\n", what);
  fprintf(stderr, "----\n%s\n----\n", text.c_str());
  if (model) print_fields("parser model", *model);
  if (ninja) print_fields("ninja", *ninja);
  abort();
}

struct NoFiles : public FileReader {
  Status ReadFile(const std::string&, std::string*, std::string* err) override {
    *err = "no files in the parser fuzzer";
    return NotFound;
  }
};

}  // namespace

// Lean's C flags hide symbols by default, and on macOS libFuzzer finds
// LLVMFuzzerInitialize with dlsym, so both entry points are exported.
#define FUZZ_EXPORT extern "C" __attribute__((visibility("default")))

FUZZ_EXPORT int LLVMFuzzerInitialize(int*, char***) {
  const char* mode = getenv("MISE_FUZZ_MODE");
  gen_mode = mode && strcmp(mode, "gen") == 0;
  // As the `main` that Lean generates for an executable: the module's
  // initialiser starts the runtime itself.
  lean_object* res = initialize_mise_MiseTest_ParseFuzz(1);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    abort();
  }
  lean_dec_ref(res);
  lean_init_task_manager();
  return 0;
}

FUZZ_EXPORT int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
  std::string text = gen_mode ? call_lean(mise_fuzz_gen, data, size)
                              : std::string(reinterpret_cast<const char*>(data), size);
  std::string model = call_lean(mise_fuzz_text, reinterpret_cast<const uint8_t*>(text.data()), text.size());
  if (model == "skip" || model.empty()) {
    if (gen_mode) fail(text, "the parser model rejects a generated manifest", nullptr, nullptr);
    return 0;
  }
  Fields all = parse_fields(model), versions, expected;
  for (auto& f : all) (f.first == "version" ? versions : expected).push_back(std::move(f));
  if (!versions_quiet(versions)) return 0;

  State state;
  NoFiles files;
  ManifestParser parser(&state, &files);
  std::string err;
  if (!parser.ParseTest(text, &err)) {
    std::string what = "the parser model accepts a manifest Ninja rejects: " + err;
    fail(text, what.c_str(), &expected, nullptr);
  }
  std::vector<bool> cyclic;
  for (const auto& f : expected) {
    if (f.first == "edge") cyclic.push_back(false);
    else if (f.first == "cyclic") cyclic.back() = true;
  }
  Fields actual = ninja_fields(state, cyclic);
  if (actual != expected) fail(text, "Ninja reads the manifest differently", &expected, &actual);
  return 0;
}
