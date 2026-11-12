// In-process build fuzzer: Ninja's build logic against the Lean model.
//
// For each input, the Lean side (MiseFuzz.lean) generates a random case and
// runs the model on it, exactly as `lake exe fuzzgen` does, and returns the
// case as JSON. This file replays the case against Ninja's own State,
// ManifestParser, BuildLog, DepsLog and Builder, linked into the same
// process, with an in-memory file system and a command runner that does
// what `test/fz.c` and the DSL's wrapper do. It checks what
// `test/fuzz.py` checks, apart from the schedule timings and
// `-t missingdeps`: the edges that ran, whether the failing edge was tried
// and whether the build failed, the contents of every output, and that
// `ninja -n` has no work to do after a build that succeeded.
//
// Files live in `Vfs`, whose clock ticks once per edit and twice per
// command (start and finish), so mtimes are exact and never tie by
// accident. `.ninja_log` and `.ninja_deps` are real files in a temporary
// directory, so that Ninja loads, appends to and recompacts them as it
// does on disk.
//
// A command reads its inputs when it starts and writes its outputs when it
// finishes. With `-j` above 1 several commands are in flight, and which one
// finishes next is chosen from the input, so the fuzzer also explores
// completion orders. Starting a command while one of its inputs is being
// written by another is reported as a schedule error.
//
// On a mismatch the case is written to $MISE_FUZZ_OUT (default
// `test/out/fuzz/inproc`) as `<n>.json`, which
// `test/fuzz.py test/out/fuzz/inproc <n>` replays against real Ninja, and
// the process aborts so that the fuzzer keeps the input.

#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#include <algorithm>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "build.h"
#include "build_log.h"
#include "deps_log.h"
#include "disk_interface.h"
#include "graph.h"
#include "manifest_parser.h"
#include "metrics.h"
#include "state.h"
#include "status.h"
#include "util.h"

#include <lean/lean.h>

extern "C" lean_object* initialize_mise_MiseFuzz(uint8_t builtin);
extern "C" lean_object* mise_fuzz_case(lean_object* input, lean_object* fins, uint8_t strict);

using std::map;
using std::optional;
using std::string;
using std::vector;

// ---------------------------------------------------------------- JSON

struct J {
  enum T { Null, Bool, Num, Str, Arr, Obj } t = Null;
  bool b = false;
  double n = 0;
  string s;
  vector<J> a;
  vector<std::pair<string, J>> o;

  const J& operator[](const char* k) const {
    static const J null;
    for (auto& kv : o)
      if (kv.first == k) return kv.second;
    return null;
  }
  bool isNull() const { return t == Null; }
};

struct JParser {
  const char* p;
  const char* end;
  void ws() {
    while (p < end && (*p == ' ' || *p == '\n' || *p == '\t' || *p == '\r')) p++;
  }
  static void put(string& out, unsigned c) {
    if (c < 0x80) {
      out += (char)c;
    } else if (c < 0x800) {
      out += (char)(0xC0 | (c >> 6));
      out += (char)(0x80 | (c & 0x3F));
    } else if (c < 0x10000) {
      out += (char)(0xE0 | (c >> 12));
      out += (char)(0x80 | ((c >> 6) & 0x3F));
      out += (char)(0x80 | (c & 0x3F));
    } else {
      out += (char)(0xF0 | (c >> 18));
      out += (char)(0x80 | ((c >> 12) & 0x3F));
      out += (char)(0x80 | ((c >> 6) & 0x3F));
      out += (char)(0x80 | (c & 0x3F));
    }
  }
  string str() {
    string out;
    p++;  // opening quote
    while (p < end && *p != '"') {
      if (*p == '\\') {
        p++;
        char c = *p++;
        switch (c) {
          case 'n': out += '\n'; break;
          case 't': out += '\t'; break;
          case 'r': out += '\r'; break;
          case 'b': out += '\b'; break;
          case 'f': out += '\f'; break;
          case 'u': {
            unsigned v = (unsigned)strtoul(string(p, 4).c_str(), nullptr, 16);
            p += 4;
            if (v >= 0xD800 && v < 0xDC00 && p + 6 <= end && p[0] == '\\' && p[1] == 'u') {
              unsigned lo = (unsigned)strtoul(string(p + 2, 4).c_str(), nullptr, 16);
              p += 6;
              v = 0x10000 + ((v - 0xD800) << 10) + (lo - 0xDC00);
            }
            put(out, v);
            break;
          }
          default: out += c;
        }
      } else {
        out += *p++;
      }
    }
    p++;  // closing quote
    return out;
  }
  J val() {
    ws();
    J j;
    if (*p == '{') {
      j.t = J::Obj;
      p++;
      ws();
      if (*p == '}') { p++; return j; }
      while (true) {
        ws();
        string k = str();
        ws();
        p++;  // ':'
        j.o.emplace_back(k, val());
        ws();
        if (*p++ == '}') break;  // else ','
      }
    } else if (*p == '[') {
      j.t = J::Arr;
      p++;
      ws();
      if (*p == ']') { p++; return j; }
      while (true) {
        j.a.push_back(val());
        ws();
        if (*p++ == ']') break;
      }
    } else if (*p == '"') {
      j.t = J::Str;
      j.s = str();
    } else if (!strncmp(p, "null", 4)) {
      p += 4;
    } else if (!strncmp(p, "true", 4)) {
      j.t = J::Bool, j.b = true, p += 4;
    } else if (!strncmp(p, "false", 5)) {
      j.t = J::Bool, p += 5;
    } else {
      j.t = J::Num;
      char* e;
      j.n = strtod(p, &e);
      p = e;
    }
    return j;
  }
};

static J parseJson(const string& s) {
  JParser jp{s.data(), s.data() + s.size()};
  return jp.val();
}

static vector<string> strs(const J& j) {
  vector<string> v;
  for (auto& x : j.a) v.push_back(x.s);
  return v;
}

// ---------------------------------------------------------------- Lean

static string leanCase(const uint8_t* data, size_t size, const string& fins) {
  lean_object* arr = lean_alloc_sarray(1, size, size);
  if (size) memcpy(lean_sarray_cptr(arr), data, size);
  // MISE_FUZZ_NO_SELF_CHECK turns the model's own checks off, as
  // FUZZGEN_NO_SELF_CHECK does for fuzzgen.
  static const bool strict = !getenv("MISE_FUZZ_NO_SELF_CHECK");
  lean_object* r = mise_fuzz_case(arr, lean_mk_string(fins.c_str()), strict);
  string out(lean_string_cstr(r), lean_string_size(r) - 1);
  lean_dec_ref(r);
  return out;
}

// ---------------------------------------------------------------- files

// The real directory that holds `.ninja_log` and `.ninja_deps`. The process
// stays in its own directory, where the fuzzer keeps its corpus.
static string g_logs;
static string logPath(const string& name) { return g_logs + "/" + name; }

struct Vfs : public DiskInterface {
  struct Entry {
    TimeStamp mtime;
    string data;
  };
  map<string, Entry> files;
  // Mtime 1 is for aged products; the clock starts above it.
  TimeStamp now = 10;

  void Tick() { ++now; }
  void Put(const string& p, const string& d) { files[p] = Entry{now, d}; }
  const Entry* Get(const string& p) const {
    auto i = files.find(p);
    return i == files.end() ? nullptr : &i->second;
  }

  TimeStamp Stat(const string& path, string* err) const override {
    auto e = Get(path);
    return e ? e->mtime : 0;
  }
  bool WriteFile(const string& path, const string& contents, bool) override {
    Put(path, contents);
    return true;
  }
  bool MakeDir(const string&) override { return true; }
  Status ReadFile(const string& path, string* contents, string* err) override {
    auto e = Get(path);
    if (!e) {
      *err = "No such file or directory";
      return NotFound;
    }
    *contents = e->data;
    return Okay;
  }
  int RemoveFile(const string& path) override { return files.erase(path) ? 0 : 1; }
};

// ---------------------------------------------------------------- the helper and the wrapper

static uint64_t feed(uint64_t h, const char* s, size_t n) {
  for (size_t i = 0; i < n; i++) {
    h ^= (unsigned char)s[i];
    h *= 1099511628211ULL;
  }
  return h;
}

static vector<string> splitWords(const string& s) {
  vector<string> w;
  size_t i = 0;
  while (i < s.size()) {
    while (i < s.size() && s[i] == ' ') i++;
    size_t j = i;
    while (j < s.size() && s[j] != ' ') j++;
    if (j > i) w.push_back(s.substr(i, j - i));
    i = j;
  }
  return w;
}

static string between(const string& s, const string& a, const string& b) {
  size_t i = s.find(a);
  if (i == string::npos) return "";
  i += a.size();
  size_t j = s.find(b, i);
  return j == string::npos ? "" : s.substr(i, j - i);
}

// What a command does to the file system, applied when it finishes.
struct Effect {
  bool ran = false;   // the helper ran (and logged its run)
  int exit = 0;
  // Path to new contents, or nullopt to delete. Paths not listed stay.
  vector<std::pair<string, optional<string>>> ops;
};

typedef std::function<const Vfs::Entry*(const string&)> View;

struct Helper {
  bool ran = false;
  int exit = 0;
  vector<string> outs;
  vector<optional<string>> vals;  // nullopt: left out (mode x) or kept (mode r)
  vector<bool> kept;
  optional<string> depfile;
  vector<string> reads;
};

// `test/fz.c` on the view `look`, with `fail` naming the output that makes it fail.
static Helper runHelper(const string& inner, const View& look, const string& fail) {
  Helper h;
  vector<string> argv = splitWords(inner);
  size_t sep = std::find(argv.begin(), argv.end(), "--") - argv.begin();
  if (argv.size() < 4 || sep < 4 || sep == argv.size()) {
    h.exit = 2;
    return h;
  }
  const string& mode = argv[1];
  bool dyn = mode.find('d') != string::npos, restat = mode.find('r') != string::npos,
       skip = mode.find('x') != string::npos;
  h.outs.assign(argv.begin() + 3, argv.begin() + sep);
  if (!fail.empty() && h.outs[0] == fail) {
    h.exit = 1;
    return h;
  }
  h.ran = true;
  for (size_t i = sep + 1; i < argv.size(); i++)
    if (std::find(h.reads.begin(), h.reads.end(), argv[i]) == h.reads.end()) h.reads.push_back(argv[i]);
  uint64_t key = 14695981039346656037ULL;
  for (size_t i = 1; i < argv.size(); i++) {
    if (i > 1) key = feed(key, " ", 1);
    key = feed(key, argv[i].data(), argv[i].size());
  }
  key = feed(key, "\n", 1);
  vector<string> texts;
  for (size_t k = 0; k < h.reads.size(); k++) {
    const Vfs::Entry* e = look(h.reads[k]);
    texts.push_back(e ? e->data : "");
    if (!dyn) continue;
    const string& s = texts.back();
    size_t i = 0;
    while (i <= s.size()) {
      size_t nl = s.find('\n', i);
      size_t e2 = nl == string::npos ? s.size() : nl;
      if (e2 - i > 8 && s.compare(i, 8, "include ") == 0) {
        string p = s.substr(i + 8, e2 - i - 8);
        if (std::find(h.reads.begin(), h.reads.end(), p) == h.reads.end()) h.reads.push_back(p);
      }
      if (nl == string::npos) break;
      i = nl + 1;
    }
  }
  for (size_t i = 0; i < h.outs.size(); i++) {
    string idx = std::to_string(i) + "\n";
    uint64_t v = feed(key, idx.data(), idx.size());
    for (auto& s : texts) {
      size_t a = 0;
      while (true) {
        size_t nl = s.find('\n', a);
        size_t e2 = nl == string::npos ? s.size() : nl;
        if (!(e2 > a && s[a] == '#')) {
          v = feed(v, s.data() + a, e2 - a);
          v = feed(v, "\n", 1);
        }
        if (nl == string::npos) break;
        a = nl + 1;
      }
      v = feed(v, "\0", 1);
    }
    char buf[32];
    snprintf(buf, sizeof buf, "%016llx\n", (unsigned long long)v);
    bool absent = skip && v % 3 == 0;
    bool keep = false;
    if (!absent && restat) {
      const Vfs::Entry* old = look(h.outs[i]);
      keep = old && old->data == buf;
    }
    h.vals.push_back(absent || keep ? optional<string>() : optional<string>(buf));
    h.kept.push_back(keep);
  }
  if (dyn) {
    string d = h.outs[0] + ":";
    for (auto& r : h.reads) d += " " + r;
    h.depfile = d + "\n";
  }
  return h;
}

// The command as `/bin/sh -c` would run it: the DSL's wrapper round the
// helper (`wrapCommand` in Mise/Frontend/Dsl.lean), or the helper alone.
static Effect runCommand(const string& cmd, const Vfs& fs, const string& fail, vector<string>* reads) {
  Effect ef;
  string inner = between(cmd, "; if ( ", " ); then ");
  bool wrapped = !inner.empty();
  if (!wrapped) inner = cmd;
  vector<string> fs_outs = wrapped ? splitWords(between(cmd, "set -- ", "; for f;")) : vector<string>();
  View plain = [&](const string& p) { return fs.Get(p); };
  // The wrapper moves every output aside before the helper runs.
  View hidden = [&](const string& p) -> const Vfs::Entry* {
    if (std::find(fs_outs.begin(), fs_outs.end(), p) != fs_outs.end()) return nullptr;
    return fs.Get(p);
  };
  Helper h = runHelper(inner, wrapped ? hidden : plain, fail);
  ef.ran = h.ran;
  *reads = h.reads;
  if (!wrapped) {
    ef.exit = h.exit;
    for (size_t i = 0; i < h.vals.size(); i++)
      if (h.vals[i])
        ef.ops.emplace_back(h.outs[i], h.vals[i]);
      else if (!h.kept[i])
        ef.ops.emplace_back(h.outs[i], optional<string>());
    if (h.depfile) ef.ops.emplace_back(h.outs[0] + ".d", h.depfile);
    return ef;
  }
  // MISE_FUZZ_BREAK=cmp breaks the wrapper on purpose, to check that the
  // harness notices: `cmp` never finds an output unchanged.
  static const bool broken = getenv("MISE_FUZZ_BREAK") && !strcmp(getenv("MISE_FUZZ_BREAK"), "cmp");
  bool restat = cmd.find("cmp -s") != string::npos && !broken;
  // What exists after the helper, among the wrapper's outputs.
  map<string, string> wrote;
  for (size_t i = 0; i < h.vals.size(); i++)
    if (h.vals[i]) wrote[h.outs[i]] = *h.vals[i];
  bool ok = h.exit == 0;
  for (auto& f : fs_outs) ok = ok && wrote.count(f);
  if (h.depfile) ef.ops.emplace_back(h.outs[0] + ".d", h.depfile);
  if (!ok) {
    // Every output is put back as it was.
    ef.exit = h.exit ? h.exit : 1;
    return ef;
  }
  for (auto& f : fs_outs) {
    const Vfs::Entry* old = fs.Get(f);
    if (old && restat && old->data == wrote[f]) continue;  // cmp equal: the old file goes back
    ef.ops.emplace_back(f, wrote[f]);
  }
  return ef;
}

// ---------------------------------------------------------------- Ninja glue

struct QuietStatus : public Status {
  void EdgeAddedToPlan(const Edge*) override {}
  void EdgeRemovedFromPlan(const Edge*) override {}
  void BuildEdgeStarted(const Edge*, int64_t) override {}
  void BuildEdgeFinished(Edge*, int64_t, int64_t, ExitStatus, const string&) override {}
  void BuildStarted() override {}
  void BuildFinished() override {}
  void SetExplanations(Explanations*) override {}
  void Info(const char*, ...) override {}
  void Warning(const char* msg, ...) override {
    if (getenv("MISE_FUZZ_VERBOSE")) {
      va_list ap;
      va_start(ap, msg);
      fprintf(stderr, "ninja: warning: ");
      vfprintf(stderr, msg, ap);
      fprintf(stderr, "\n");
      va_end(ap);
    }
  }
  void Error(const char* msg, ...) override {
    va_list ap;
    va_start(ap, msg);
    fprintf(stderr, "ninja: error: ");
    vfprintf(stderr, msg, ap);
    fprintf(stderr, "\n");
    va_end(ap);
  }
};

struct Rng {
  uint64_t s;
  uint64_t next() {
    uint64_t z = (s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
  }
  size_t below(size_t n) { return n ? next() % n : 0; }
};

struct Mismatch {
  string kind, msg;
};

struct Runner : public CommandRunner {
  struct Job {
    Edge* edge;
    Effect effect;
  };
  Vfs* fs;
  Rng* rng;
  size_t parallelism;
  string fail;
  vector<Job> active;
  vector<string> ran;  // first output of each helper run, in order
  bool tried = false;
  optional<Mismatch>* bad;

  size_t CanRunMore() const override { return parallelism - active.size(); }

  bool StartCommand(Edge* edge) override {
    // Every input, order-only ones included, must be done.
    for (Node* in : edge->inputs_)
      for (auto& j : active)
        if (in->in_edge() == j.edge && !*bad)
          *bad = Mismatch{"schedule", edge->outputs_[0]->path() + " started while " + in->path() + " was being built"};
    vector<string> reads;
    Effect ef = runCommand(edge->EvaluateCommand(), *fs, fail, &reads);
    for (auto& r : reads)
      for (auto& j : active)
        for (Node* o : j.edge->outputs_)
          if (o->path() == r && !*bad)
            *bad = Mismatch{"schedule", edge->outputs_[0]->path() + " read " + r + " while it was being built"};
    string first = edge->outputs_[0]->path();
    if (first == fail) tried = true;
    if (ef.ran) ran.push_back(first);
    fs->Tick();
    active.push_back(Job{edge, ef});
    return true;
  }

  bool WaitForCommand(Result* result) override {
    if (active.empty()) return false;
    size_t i = rng->below(active.size());
    Job j = active[i];
    active.erase(active.begin() + i);
    fs->Tick();
    for (auto& op : j.effect.ops)
      if (op.second)
        fs->Put(op.first, *op.second);
      else
        fs->RemoveFile(op.first);
    result->edge = j.edge;
    result->status = j.effect.exit == 0 ? ExitSuccess : ExitFailure;
    return true;
  }

  vector<Edge*> GetActiveEdges() override {
    vector<Edge*> v;
    for (auto& j : active) v.push_back(j.edge);
    return v;
  }
  void Abort() override { active.clear(); }
};

// One `ninja` process: load the manifest and the logs, build, close the logs.
struct Ninja : public BuildLogUser {
  State state;
  Vfs* fs;
  BuildLog build_log;
  DepsLog deps_log;
  QuietStatus status;

  bool IsPathDead(StringPiece s) const override {
    Node* n = state.LookupNode(s);
    if (n && n->in_edge()) return false;
    string err;
    return fs->Stat(s.AsString(), &err) == 0;
  }

  bool Load(bool dry_run, string* err) {
    ManifestParser parser(&state, fs);
    if (!parser.Load("build.ninja", err)) return false;
    if (build_log.Load(logPath(".ninja_log"), err) == LOAD_ERROR) return false;
    err->clear();
    if (!dry_run && !build_log.OpenForWrite(logPath(".ninja_log"), *this, err)) return false;
    if (deps_log.Load(logPath(".ninja_deps"), &state, err) == LOAD_ERROR) return false;
    err->clear();
    if (!dry_run && !deps_log.OpenForWrite(logPath(".ninja_deps"), err)) return false;
    return true;
  }

  bool Targets(const vector<string>& names, vector<Node*>* out, string* err) {
    if (names.empty()) {
      *out = state.DefaultNodes(err);
      return err->empty();
    }
    for (auto& t : names) {
      Node* n = state.LookupNode(t);
      if (!n) {
        *err = "unknown target " + t;
        return false;
      }
      out->push_back(n);
    }
    return true;
  }

  ~Ninja() {
    build_log.Close();
    deps_log.Close();
    // Ninja never frees its graph, since a process builds once; here many
    // builds share a process.
    for (Edge* e : state.edges_) delete e;
    for (auto& kv : state.paths_) delete kv.second;
  }
};

struct BuildResult {
  bool failed = false;
  bool tried = false;
  vector<string> ran;
};

static optional<Mismatch> runNinja(Vfs& fs, Rng& rng, int jobs, const vector<string>& targets, const string& fail,
                                   bool k0, BuildResult* res) {
  optional<Mismatch> bad;
  Ninja n;
  n.fs = &fs;
  string err;
  if (!n.Load(false, &err)) return Mismatch{"load", err};
  vector<Node*> nodes;
  if (!n.Targets(targets, &nodes, &err)) return Mismatch{"targets", err};
  BuildConfig config;
  config.verbosity = BuildConfig::QUIET;
  config.parallelism = jobs;
  config.failures_allowed = k0 ? INT_MAX : 1;
  Builder builder(&n.state, config, &n.build_log, &n.deps_log, &fs, &n.status, GetTimeMillis());
  Runner* runner = new Runner;
  runner->fs = &fs;
  runner->rng = &rng;
  runner->parallelism = jobs;
  runner->fail = fail;
  runner->bad = &bad;
  builder.command_runner_.reset(runner);
  for (Node* t : nodes)
    if (!builder.AddTarget(t, &err)) {
      bad = Mismatch{"scan", err};
      break;
    }
  if (!bad && !builder.AlreadyUpToDate()) {
    ExitStatus st = builder.Build(&err);
    res->failed = st != ExitSuccess;
  }
  res->tried = runner->tried;
  res->ran = runner->ran;
  return bad;
}

// `ninja -n`: a dry run that must find nothing to do.
static optional<Mismatch> upToDate(Vfs& fs, const vector<string>& targets) {
  Ninja n;
  n.fs = &fs;
  string err;
  if (!n.Load(true, &err)) return Mismatch{"load", err};
  vector<Node*> nodes;
  if (!n.Targets(targets, &nodes, &err)) return Mismatch{"targets", err};
  BuildConfig config;
  config.verbosity = BuildConfig::QUIET;
  config.dry_run = true;
  Builder builder(&n.state, config, &n.build_log, &n.deps_log, &fs, &n.status, GetTimeMillis());
  for (Node* t : nodes)
    if (!builder.AddTarget(t, &err)) return Mismatch{"scan", err};
  if (!builder.AlreadyUpToDate()) {
    string dirty;
    for (Edge* e : n.state.edges_)
      if (!e->outputs_.empty() && e->outputs_[0]->dirty()) dirty += " " + e->outputs_[0]->path();
    return Mismatch{"rerun", "ninja -n has work to do:" + dirty};
  }
  return std::nullopt;
}

static string join(const vector<string>& v) {
  string s;
  for (auto& x : v) s += (s.empty() ? "" : " ") + x;
  return s;
}

// ---------------------------------------------------------------- replay

static const int kJobs[] = {1, 2, 8, 64};

// What the replays covered, for the standalone driver.
static struct {
  long steps, edges, stops, failed, parallel;
} stats;

static optional<Mismatch> replay(const uint8_t* data, size_t size, const string& first) {
  Rng rng{feed(0x6d697365ULL, (const char*)data, size)};
  J c = parseJson(first);
  vector<J> steps = c["steps"].a;
  string fins;
  Vfs fs;
  unlink(logPath(".ninja_log").c_str());
  unlink(logPath(".ninja_deps").c_str());
  for (size_t i = 0; i < steps.size(); i++) {
    J s = steps[i];
    int jobs = kJobs[rng.below(4)];
    string where = "step " + std::to_string(i) + " (" + join(strs(s["edits"])) + ", -j" + std::to_string(jobs) + ")";
    for (auto& kv : s["write"].o) {
      fs.Tick();
      fs.Put(kv.first, kv.second.s);
    }
    for (auto& p : strs(s["delete"]))
      if (p == ".ninja_log" || p == ".ninja_deps")
        unlink(logPath(p).c_str());
      else
        fs.RemoveFile(p);
    for (auto& p : strs(s["age"]))
      if (fs.files.count(p)) fs.files[p].mtime = 1;
    fs.Tick();
    fs.Put("build.ninja", s["ninja"].s);
    fs.Tick();
    string fail = s["fail"].isNull() ? "" : s["fail"].s;
    bool stop = s["stop"].b;
    BuildResult r;
    if (auto m = runNinja(fs, rng, jobs, strs(s["targets"]), fail, !stop, &r)) return Mismatch{m->kind, where + ": " + m->msg};
    vector<string> ran = r.ran;
    std::sort(ran.begin(), ran.end());
    for (size_t k = 1; k < ran.size(); k++)
      if (ran[k] == ran[k - 1]) return Mismatch{"twice", where + ": " + ran[k] + " ran twice"};
    if (stop) {
      fins += std::to_string(i - 1) + (r.tried ? " 1" : " 0");
      for (auto& o : r.ran) fins += " " + o;
      fins += "\n";
      string again = leanCase(data, size, fins);
      if (again.rfind("error: ", 0) == 0) return Mismatch{"stop", where + ": the model rejects the edges Ninja ran: " + again};
      steps = parseJson(again)["steps"].a;
      s = steps[i];
    }
    if (r.tried != s["tried"].b)
      return Mismatch{"tried", where + ": failing edge tried " + std::to_string(r.tried) + ", model says " +
                                   std::to_string(s["tried"].b)};
    if (r.failed != s["failed"].b)
      return Mismatch{"exit", where + ": build failed " + std::to_string(r.failed) + ", model says " +
                                  std::to_string(s["failed"].b)};
    stats.steps++;
    stats.edges += ran.size();
    stats.stops += stop;
    stats.failed += r.failed;
    stats.parallel += jobs > 1 && ran.size() > 1;
    vector<string> want = strs(s["ran"]);
    if (ran != want) return Mismatch{"ran", where + ": Ninja ran [" + join(ran) + "], the model [" + join(want) + "]"};
    for (auto& kv : s["products"].o) {
      const Vfs::Entry* e = fs.Get(kv.first);
      bool ok = e ? (!kv.second.isNull() && e->data == kv.second.s) : (kv.second.isNull() || kv.second.s.empty());
      if (!ok)
        return Mismatch{"contents", where + ": " + kv.first + " holds " + (e ? e->data : "nothing") + ", the model says " +
                                        (kv.second.isNull() ? "nothing" : kv.second.s)};
    }
    if (r.failed) continue;
    if (auto m = upToDate(fs, strs(s["targets"]))) return Mismatch{m->kind, where + ": " + m->msg};
  }
  return std::nullopt;
}

static string outDir() {
  const char* d = getenv("MISE_FUZZ_OUT");
  return d ? d : "";
}

static void report(const string& json, const Mismatch& m) {
  string dir = outDir();
  int k = 0;
  string path;
  do path = dir + "/" + std::to_string(k++) + ".json";
  while (access(path.c_str(), F_OK) == 0);
  FILE* f = fopen(path.c_str(), "wb");
  if (f) {
    fwrite(json.data(), 1, json.size(), f);
    fclose(f);
  }
  fprintf(stderr, "mise-fuzz: %s: %s\nmise-fuzz: case written to %s\n", m.kind.c_str(), m.msg.c_str(), path.c_str());
}

static void init() {
  static bool done = false;
  if (done) return;
  done = true;
  lean_object* r = initialize_mise_MiseFuzz(1);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(r)) {
    lean_io_result_show_error(r);
    abort();
  }
  lean_dec_ref(r);
  string out = outDir();
  if (out.empty()) out = "test/out/fuzz/inproc";
  string mk = "mkdir -p '" + out + "'";
  if (system(mk.c_str()) != 0) abort();
  setenv("MISE_FUZZ_OUT", out.c_str(), 1);
  const char* tmp = getenv("TMPDIR");
  string tmpl = string(tmp && *tmp ? tmp : "/tmp") + "/mise-fuzz-XXXXXX";
  if (!mkdtemp(&tmpl[0])) abort();
  g_logs = tmpl;
}

// Replay one input. Returns 0 when Ninja and the model agree.
static int one(const uint8_t* data, size_t size) {
  init();
  string json = leanCase(data, size, "");
  if (json.rfind("error: ", 0) == 0) {
    report("{}", Mismatch{"model", json});
    return 1;
  }
  if (auto m = replay(data, size, json)) {
    report(json, *m);
    return 1;
  }
  return 0;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
  if (one(data, size)) abort();
  return 0;
}

#ifdef MISE_FUZZ_STANDALONE
// Without a fuzzer: `harness N [SEED]` replays N inputs of eight bytes
// counting up from SEED and prints the rate; `harness FILE...` replays
// the inputs in the files.
int main(int argc, char** argv) {
  if (argc >= 2 && access(argv[1], F_OK) == 0) {
    int bad = 0;
    for (int i = 1; i < argc; i++) {
      FILE* f = fopen(argv[i], "rb");
      string s;
      char buf[4096];
      size_t n;
      while ((n = fread(buf, 1, sizeof buf, f)) > 0) s.append(buf, n);
      fclose(f);
      bad += one((const uint8_t*)s.data(), s.size());
    }
    return bad ? 1 : 0;
  }
  long n = argc >= 2 ? atol(argv[1]) : 100;
  uint64_t seed = argc >= 3 ? strtoull(argv[2], nullptr, 10) : 0;
  init();
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  int bad = 0;
  double lean_s = 0;
  for (long i = 0; i < n; i++) {
    uint64_t x = seed + i;
    struct timespec a, b;
    clock_gettime(CLOCK_MONOTONIC, &a);
    string json = leanCase((const uint8_t*)&x, sizeof x, "");
    clock_gettime(CLOCK_MONOTONIC, &b);
    lean_s += (b.tv_sec - a.tv_sec) + (b.tv_nsec - a.tv_nsec) / 1e9;
    if (json.rfind("error: ", 0) == 0) {
      report("{}", Mismatch{"model", json});
      bad++;
      continue;
    }
    if (auto m = replay((const uint8_t*)&x, sizeof x, json)) {
      report(json, *m);
      bad++;
    }
  }
  clock_gettime(CLOCK_MONOTONIC, &t1);
  double s = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
  printf("%ld cases in %.2f s: %.1f cases/s; model %.2f s, Ninja %.2f s; %d mismatches\n", n, s, n / s, lean_s,
         s - lean_s, bad);
  printf("%ld steps (%ld stopped, %ld failed, %ld parallel with several edges), %ld edges run\n", stats.steps,
         stats.stops, stats.failed, stats.parallel, stats.edges);
  return bad ? 1 : 0;
}
#endif
