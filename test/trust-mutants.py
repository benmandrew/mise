#!/usr/bin/env python3
"""Mutation testing of the definitions the theorems are stated in.

Each mutant is one small edit to a definition that a statement in
`Mise/Theorems.lean` uses, and makes at least one of those theorems weaker:
a hypothesis that holds less often, or a conclusion that says less. A proof
cannot catch such a mutant, because the weaker theorem is still true, so a
test in `test/MiseTest/` must. (Some mutants also make another theorem
false, but the tests should still pin each definition by themselves.)
Mutants that make a theorem stronger or false are the proofs' job and are
not listed. Proofs do not tell the two apart: they break on almost any
change to a definition they unfold, equivalent ones included.

The driver

1. copies the tree to `test/out/trust-mutants/tree`, never touching the real
   tree;
2. in the copy, replaces the body of every theorem in `Mise/` with `sorry`,
   and builds the library with `debug.byAsSorry`, which does the same for
   the `by` proofs inside definitions. A mutant then breaks no proof, and
   the build depends only on the definitions. The copy's tests use
   `#eval!`, because `#eval` refuses a value that depends on `sorry`;
3. builds `MiseTest` on the unmutated copy, which must succeed;
4. for each mutant, applies the edit and builds `MiseTest` again.

A mutant is killed when a test fails. The kill is "evaluates" when `decide`
or `#guard` computed a false result, and "elaborates" when a test no longer
type-checks: an unknown constructor, a wrong number of arguments, or a proof
step that fails. A mutant that breaks the library itself is an error, since
the tests never run. The results table goes to
`test/out/trust-mutants/results.md`. The exit status is 1 when a mutant
survives or is an error.

usage: trust-mutants.py [MUTANT...]
"""
import argparse
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "test" / "out" / "trust-mutants"
TREE = OUT / "tree"

SOUND = "Mise/Model/Sound.lean"
SPEC = "Mise/Spec/Basic.lean"
THMS = "Mise/Theorems.lean"
BASIC = "Mise/Model/Basic.lean"
GRAPH = "Mise/Frontend/Graph.lean"
TASK = "Mise/Task/Basic.lean"
CMP = "Mise/Model/Cmp.lean"

# (name, definition, file, what it does, old text, new text). Each old text
# occurs exactly once in its file.
MUTANTS = [
    ("reach-no-init", "Reach", SOUND, "no start state, so nothing is reachable",
     "  | init {st : St V} : st.Fresh → (∀ p, st.log p = none) → (∀ p, st.deps p = none) → Reach es st\n", ""),
    ("reach-no-edit", "Reach", SOUND, "drop source edits",
     "  | edit {st : St V} (p : Path) (v : V) : Reach es st → (∀ e ∈ es, p ∉ e.outs) → Reach es (st.edit p v)\n", ""),
    # Deleting `step` would leave `Reach` without `sem`, so Lean would drop
    # that argument and every use of `Reach` would fail to type-check.
    ("reach-no-step", "Reach", SOUND, "no edge can be visited",
     "Reach es st → e ∈ es → Reach es (st.step sem e)", "Reach es st → e ∈ ([] : List MEdge) → Reach es (st.step sem e)"),
    ("reach-clock-0", "Reach", SOUND, "a start state has clock 0",
     "st.Fresh → (∀ p, st.log p = none)", "st.clock = 0 → st.Fresh → (∀ p, st.log p = none)"),
    ("reach-edit-unread", "Reach", SOUND, "only a path no edge reads can be edited",
     "(∀ e ∈ es, p ∉ e.outs) → Reach es (st.edit p v)", "(∀ e ∈ es, p ∉ e.outs ∧ p ∉ e.ins) → Reach es (st.edit p v)"),
    ("reach-step-first", "Reach", SOUND, "only the first edge can be visited",
     "Reach es st → e ∈ es → Reach es (st.step sem e)", "Reach es st → e ∈ es.take 1 → Reach es (st.step sem e)"),
    ("fresh-strict", "St.Fresh", BASIC, "every mtime is earlier than the clock",
     "(∀ p v t, st.fs p = some (v, t) → t ≤ st.clock)", "(∀ p v t, st.fs p = some (v, t) → t < st.clock)"),
    ("correct-src-true", "Correct", SPEC, "sources may hold anything",
     "  (∀ k, b.isSource k = true → R k = S k) ∧\n", "  True ∧\n"),
    ("correct-tgt-true", "Correct", SPEC, "targets may hold anything",
     "  (∀ k, b.isSource k = false → R k = (b.task k).run R)\n", "  True\n"),
    ("spec-self", "Spec", THMS, "compare the result with its own sources",
     "(g.spec sem).Correct st.content (f st).content", "(g.spec sem).Correct (f st).content (f st).content"),
    ("cmdtask-no-ins", "cmdTask", GRAPH, "a static command ignores its inputs",
     "(fetchAll ins).bind fun vs => .pure (sem.exec cmd vs)", ".pure (sem.exec cmd [])"),
    ("cmdtask-static", "cmdTask", GRAPH, "a depfile command is treated as static",
     "  if dyn then sem.dyn cmd else", "  if false then sem.dyn cmd else"),
    ("issource-never", "Graph.isSource", GRAPH, "no path is a source",
     "def Graph.isSource (g : Graph) (k : Path) : Bool := (findOut GEdge.allOuts k g.edges).isNone",
     "def Graph.isSource (_ : Graph) (_ : Path) : Bool := false"),
    ("checks-true", "Checks", THMS, "every path is checked",
     "∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ p ∈ D", "True"),
    ("checks-outs", "Checks", THMS, "an edge's own outputs are checked",
     "st.effIns e o = some D ∧ p ∈ D", "st.effIns e o = some D ∧ (p ∈ D ∨ p ∈ e.outs)"),
    ("checks-oo", "Checks", THMS, "order-only inputs are checked",
     "st.effIns e o = some D ∧ p ∈ D", "st.effIns e o = some D ∧ (p ∈ D ∨ p ∈ e.oo)"),
    ("ran-empty", "ran", THMS, "a build runs no edge",
     "List MEdge := (buildTrace sem (edges g) st).2", "List MEdge := (buildTrace sem (edges g) st).2.take 0"),
    ("ran-first", "ran", THMS, "a build runs at most its first dirty edge",
     "List MEdge := (buildTrace sem (edges g) st).2", "List MEdge := (buildTrace sem (edges g) st).2.take 1"),
    ("edits-ignored", "St.edits", BASIC, "a list of edits changes nothing",
     "  | (p, v) :: es => (st.edit p v).edits es", "  | (_, _) :: es => st.edits es"),
    ("order-exact", "ValidOrder", THMS, "manifest order is the only valid order",
     "es.Perm (edges g) ∧ Sched es", "es = edges g ∧ Sched es"),
    ("sched-no-deps", "Sched", BASIC, "no edge reads an earlier edge's output",
     "Disjoint e.reads e'.outs ∧ Disjoint e.outs e'.outs",
     "Disjoint e.reads e'.outs ∧ Disjoint e'.reads e.outs ∧ Disjoint e.outs e'.outs"),
    ("dynok-no-source", "DynOK", GRAPH, "a depfile command may not read an undeclared source",
     "fun k => g.isSource k = true ∨ k ∈ e.allIns", "fun k => k ∈ e.allIns"),
    ("dynok-no-oo", "DynOK", GRAPH, "a depfile command may not read an order-only input",
     "fun k => g.isSource k = true ∨ k ∈ e.allIns", "fun k => g.isSource k = true ∨ k ∈ e.inputs"),
    ("fetchesonly-pure", "FetchesOnly", TASK, "only a task that fetches nothing qualifies",
     "  | fetch (k : K) (c : V → Task K V α) :\n      P k → (∀ v, FetchesOnly P (c v)) → FetchesOnly P (.fetch k c)\n", ""),
    ("wrapped-noop", "runWrapped", CMP, "a wrapped run changes nothing",
     "  if r.2 then { st.run sem e with fs := r.1 } else { st with fs := r.1 }", "  let _ := r\n  st"),
    ("wrapped-no-log", "runWrapped", CMP, "a successful wrapped run writes no log entry",
     "{ st.run sem e with fs := r.1 }", "{ st with fs := r.1, clock := st.clock + 1 }"),
]

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|example)\b")
OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSE = set(OPEN.values())
CHAR = re.compile(r"'(?:\\.|[^\\'])'")
LET = re.compile(r"\b(?:let|have)\b")


def body_start(d):
    """The index in declaration `d` where its proof starts: the first `:=`, or
    the first line that starts with `|`, outside brackets, comments and
    strings."""
    depth, i = 0, 0
    while i < len(d):
        c = d[i]
        if d.startswith("--", i):
            i = d.find("\n", i)
            if i < 0:
                return None
            continue
        if d.startswith("/-", i):
            nest, i = 1, i + 2
            while nest and i < len(d):
                if d.startswith("/-", i):
                    nest, i = nest + 1, i + 2
                elif d.startswith("-/", i):
                    nest, i = nest - 1, i + 2
                else:
                    i += 1
            continue
        if c == '"':
            i += 1
            while i < len(d) and d[i] != '"':
                i += 2 if d[i] == "\\" else 1
        elif c == "'" and (i == 0 or not (d[i - 1].isalnum() or d[i - 1] in "_'!?")) and (m := CHAR.match(d, i)):
            i = m.end() - 1
        elif c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and d.startswith(":=", i) and not LET.search(d, d.rfind("\n", 0, i) + 1, i):
            return i
        elif depth == 0 and c == "\n" and d.startswith("  |", i + 1) and not d[:i].rstrip().endswith("with"):
            return i
        i += 1
    return None


def sorry_theorems(text):
    """Replace the proof of every top-level theorem with `sorry`. A
    declaration runs to the next line that starts in column 0."""
    lines = text.split("\n")
    out, i, n = [], 0, 0
    while i < len(lines):
        if not DECL.match(lines[i]):
            out.append(lines[i])
            i += 1
            continue
        j = i + 1
        while j < len(lines) and (not lines[j] or lines[j][0] in " \t"):
            j += 1
        while j > i + 1 and not lines[j - 1].strip():
            j -= 1
        d = "\n".join(lines[i:j])
        k = body_start(d)
        if k is None:
            sys.exit(f"cannot find the proof of: {lines[i]}")
        out.append(d[:k].rstrip() + " := sorry")
        n += 1
        i = j
    return "\n".join(out), n


def sh(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd or TREE, capture_output=True, text=True)


def copy_tree():
    """Copy the sources and the build directory, with copy-on-write clones
    where the file system has them."""
    shutil.rmtree(TREE, ignore_errors=True)
    (TREE / "test").mkdir(parents=True)
    items = [".lake", "Mise", "Main.lean", "Mise.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json", "fuzz"]
    tests = [p.name for p in (ROOT / "test").iterdir() if p.name != "out"]
    for src, dst in [(items, TREE), ([f"test/{t}" for t in tests], TREE / "test")]:
        args = [str(ROOT / s) for s in src] + [str(dst)]
        if sys.platform != "darwin" or sh(["/bin/cp", "-Rc", *args], cwd=ROOT).returncode != 0:
            subprocess.run(["cp", "-R", *args], check=True)


def prepare():
    """Turn every proof in the copy's library into `sorry`."""
    lake = TREE / "lakefile.toml"
    cfg = lake.read_text()
    lib = '[[lean_lib]]\nname = "Mise"\n'
    if cfg.count(lib) != 1:
        sys.exit("lakefile.toml: cannot find the Mise library")
    lake.write_text(cfg.replace(lib, lib + 'moreLeanArgs = ["-Ddebug.byAsSorry=true"]\n'))
    total = 0
    for f in sorted((TREE / "Mise").rglob("*.lean")):
        text, n = sorry_theorems(f.read_text())
        f.write_text(text)
        total += n
    # `#eval` refuses a value that depends on `sorry`, which a definition
    # with a proof inside it now does.
    for f in sorted((TREE / "test" / "MiseTest").rglob("*.lean")):
        f.write_text(re.sub(r"^#eval ", "#eval! ", f.read_text(), flags=re.M))
    return total


ERR = re.compile(r"^error: (?:\./)*(\S+?\.lean):(\d+):\d+: ", re.M)


def build():
    """The errors of `lake build MiseTest`, as (file, line, message)."""
    r = sh(["lake", "build", "MiseTest"])
    text = r.stdout + r.stderr
    marks = list(ERR.finditer(text))
    errs = []
    for a, b in zip(marks, marks[1:] + [None]):
        msg = text[a.end():b.start() if b else len(text)]
        errs.append((a.group(1), int(a.group(2)), msg))
    if r.returncode != 0 and not errs:
        errs.append(("?", 0, text[-1500:]))
    return errs


def verdict(errs):
    """(verdict, kind, where) for one mutant's build errors."""
    if not errs:
        return "SURVIVED", "", ""
    lib = [e for e in errs if e[0].startswith("Mise/") or e[0] == "?"]
    if lib:
        f, line, msg = lib[0]
        return "error", "library", f"`{f}:{line}`: {msg.strip().splitlines()[0][:80]}"
    evaluates = any("proved that the proposition" in m or "did not evaluate to `true`" in m for _, _, m in errs)
    where = sorted({f"{f.removeprefix('test/MiseTest/')}:{line}" for f, line, _ in errs})
    return "killed", "evaluates" if evaluates else "elaborates", ", ".join(where[:4]) + (" …" if len(where) > 4 else "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("only", nargs="*", help="run only these mutants")
    a = ap.parse_args()
    unknown = set(a.only) - {m[0] for m in MUTANTS}
    if unknown:
        sys.exit(f"unknown mutants: {sorted(unknown)}")
    todo = [m for m in MUTANTS if not a.only or m[0] in a.only]
    start = time.time()
    copy_tree()
    for name, _, f, _, old, _ in todo:
        c = (TREE / f).read_text().count(old)
        if c != 1:
            sys.exit(f"{name}: the text to replace occurs {c} times in {f}")
    n = prepare()
    t = time.time()
    errs = build()
    print(f"unmutated, {n} theorems as sorry: {'fails' if errs else 'passes'}, {time.time() - t:.0f}s", flush=True)
    if errs:
        for f, line, msg in errs[:5]:
            print(f"  {f}:{line}: {msg.strip()[:300]}")
        sys.exit("the unmutated tests fail; mutant results would mean nothing")

    rows = []
    for name, defn, f, what, old, new in todo:
        src = (TREE / f).read_text()
        (TREE / f).write_text(src.replace(old, new))
        t = time.time()
        v, kind, where = verdict(build())
        (TREE / f).write_text(src)
        rows.append((name, defn, what, v, kind, where))
        print(f"{name}: {v}{f' ({kind})' if kind else ''}; {where}; {time.time() - t:.0f}s", flush=True)

    k = sum(r[3] == "killed" for r in rows)
    lines = [f"{k} of {len(rows)} mutants killed, {time.time() - start:.0f} s.", "",
             "| Mutant | Definition | Change | Verdict | Kill | Where |", "|---|---|---|---|---|---|"]
    lines += [f"| `{r[0]}` | `{r[1]}` | {r[2]} | {r[3]} | {r[4]} | {r[5]} |" for r in rows]
    report = "\n".join(lines) + "\n"
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "results.md").write_text(report)
    print()
    print(report)
    return 0 if k == len(rows) else 1


if __name__ == "__main__":
    sys.exit(main())
