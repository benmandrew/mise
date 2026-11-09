#!/usr/bin/env python3
"""Stage 6 and 7 property harness against real Ninja.

For each example, run random sequences of edits. A sequence starts with a
clean build, then applies edits one at a time, running `ninja` after each
with a random `-j` level, so that Ninja runs independent commands in
different orders.
After every build it checks three things:

1. every build product equals, byte for byte, the product of a clean build
   of the same sources in a separate directory;
2. `ninja -n` reports no work;
3. `ninja -t missingdeps` finds nothing.

Edits change a source file, add or remove an `#include`, change the
generator script, add a comment to `config.in` (which leaves the generated
header the same, so the `restat` generator keeps it), or change `cflags` in
the DSL and regenerate the manifest. After a comment edit the harness also
checks that only the generator ran (early cutoff).

usage: props.py [--sequences N] [--seed S] [EXAMPLE...]
"""
import argparse
import hashlib
import random
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GEN = ROOT / ".lake" / "build" / "bin" / "gen"
OUT = ROOT / "test" / "out" / "props"
FLAGS = ["-O2 -Wall", "-O0", "-O1 -DMISE_FLAG=1"]
JOBS = ["-j1", "-j2", "-j8"]


class HelloC:
    name = "hello-c"
    products = ["build/main.o", "build/greet.o", "build/hello"]

    def initial(self):
        return {"main": 0, "greet": 0, "header": 0, "flag": 0}

    def render(self, s):
        return {
            "greet.h": f"#pragma once\n#define GREET_N {s['header']}\nvoid greet(void);\n",
            "greet.c": '#include <stdio.h>\n#include "greet.h"\n'
                       f'void greet(void) {{ printf("Hello %d %d\\n", GREET_N, {s["greet"]}); }}\n',
            "main.c": '#include "greet.h"\n'
                      f'int main(void) {{ greet(); return {s["main"]} * 0; }}\n',
        }

    def edits(self):
        return [("bump", "main"), ("bump", "greet"), ("bump", "header"), ("flag",)]


class GenHeader:
    name = "gen-header"
    products = ["build/config.h", "build/main.o", "build/util.o", "build/app"]
    generator = (ROOT / "examples" / "gen-header" / "gen-config.py").read_text()

    def initial(self):
        return {"main": 0, "util": 0, "utilh": 0, "extra": 0, "cfg": 0, "gen": 0, "note": 0,
                "main_extra": False, "util_extra": False, "flag": 0}

    @staticmethod
    def c_file(includes, body):
        lines = ["#include <stdio.h>"] + [f'#include "{h}"' for h in includes]
        lines += ["#ifndef EXTRA", "#define EXTRA -1", "#endif", body, ""]
        return "\n".join(lines)

    def render(self, s):
        main_inc = ["config.h"] + (["extra.h"] if s["main_extra"] else []) + ["util.h"]
        util_inc = ["config.h", "util.h"] + (["extra.h"] if s["util_extra"] else [])
        return {
            "main.c": self.c_file(main_inc, 'int main(void) { greet("mise", TIMES); '
                                  f'printf("main %d %d\\n", {s["main"]}, EXTRA); return 0; }}'),
            "util.c": self.c_file(util_inc, "void greet(const char *who, int times) { "
                                  'for (int i = 0; i < times; i++) printf("%s, %s! %d %d\\n", '
                                  f'GREETING, who, {s["util"]}, EXTRA); }}'),
            "util.h": f"#pragma once\nvoid greet(const char *who, int times);\n/* {s['utilh']} */\n",
            "extra.h": f"#pragma once\n#define EXTRA {s['extra']}\n",
            "config.in": f'# note {s["note"]}\nGREETING="Hello {s["cfg"]}"\nTIMES={1 + s["cfg"] % 3}\n',
            "gen-config.py": self.generator + f"# version {s['gen']}\n",
        }

    def edits(self):
        return [("bump", k) for k in ["main", "util", "utilh", "extra", "cfg", "gen", "note"]] + \
               [("toggle", "main_extra"), ("toggle", "util_extra"), ("flag",)]


def run(cmd, cwd):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} failed in {cwd}:\n{r.stdout}{r.stderr}")
    return r.stdout


def write_files(d, files, old=None):
    for name, text in files.items():
        if old is None or old.get(name) != text:
            (d / name).write_text(text)


def gen(d, flag):
    run([str(GEN), "--set", f"cflags={FLAGS[flag]}", str(d)], ROOT)


def products(d, names):
    return {n: (d / n).read_bytes() for n in names}


class Checker:
    def __init__(self, ex):
        self.ex = ex
        self.cache = {}
        self.clean_builds = 0

    def clean(self, files, manifest):
        h = hashlib.sha256()
        for name in sorted(files):
            h.update(name.encode() + b"\0" + files[name].encode() + b"\0")
        h.update(manifest)
        key = h.hexdigest()
        if key not in self.cache:
            d = OUT / "clean" / self.ex.name
            shutil.rmtree(d, ignore_errors=True)
            d.mkdir(parents=True)
            write_files(d, files)
            (d / "build.ninja").write_bytes(manifest)
            run(["ninja"], d)
            self.cache[key] = products(d, self.ex.products)
            self.clean_builds += 1
        return self.cache[key]

    def check(self, d, files, where):
        expected = self.clean(files, (d / "build.ninja").read_bytes())
        actual = products(d, self.ex.products)
        for n in self.ex.products:
            if actual[n] != expected[n]:
                raise AssertionError(f"{where}: {n} differs from a clean build")
        if "no work to do" not in run(["ninja", "-n"], d):
            raise AssertionError(f"{where}: ninja -n has work to do")
        md = run(["ninja", "-t", "missingdeps"], d)
        if "No missing dependencies" not in md:
            raise AssertionError(f"{where}: missingdeps reported:\n{md}")


def sequence(ex, checker, rng, idx):
    d = OUT / "inc" / ex.name
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir(parents=True)
    state = ex.initial()
    files = ex.render(state)
    write_files(d, files)
    gen(d, state["flag"])
    run(["ninja", rng.choice(JOBS)], d)
    history = ["clean build"]
    checker.check(d, files, f"sequence {idx}, after {history}")
    for _ in range(rng.randint(1, 6)):
        edit = rng.choice(ex.edits())
        new = dict(state)
        if edit[0] == "bump":
            new[edit[1]] = rng.choice([v for v in range(5) if v != state[edit[1]]])
        elif edit[0] == "toggle":
            new[edit[1]] = not state[edit[1]]
        else:
            new["flag"] = rng.choice([i for i in range(len(FLAGS)) if i != state["flag"]])
        new_files = ex.render(new)
        write_files(d, new_files, files)
        if new["flag"] != state["flag"]:
            gen(d, new["flag"])
        before = {n: (d / n).stat().st_mtime_ns for n in ex.products}
        out = run(["ninja", rng.choice(JOBS)], d)
        history.append(" ".join(map(str, edit)))
        if edit == ("bump", "note"):
            after = {n: (d / n).stat().st_mtime_ns for n in ex.products}
            if after != before or out.count("GEN ") != 1 or "CC " in out or "LINK " in out:
                raise AssertionError(f"sequence {idx}, after {history}: no early cutoff:\n{out}")
        state, files = new, new_files
        checker.check(d, files, f"sequence {idx}, after {history}")
    return len(history) - 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequences", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("examples", nargs="*", default=["hello-c", "gen-header"])
    args = ap.parse_args()
    examples = {e.name: e for e in [HelloC(), GenHeader()]}
    rng = random.Random(args.seed)
    for name in args.examples:
        ex = examples[name]
        checker = Checker(ex)
        edits = sum(sequence(ex, checker, rng, i) for i in range(args.sequences))
        print(f"props {name}: {args.sequences} sequences, {edits} edits, "
              f"{checker.clean_builds} distinct clean builds, all checks passed")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, RuntimeError) as e:
        print(f"FAIL: {e}", file=sys.stderr)
        sys.exit(1)
