#!/usr/bin/env python3
"""Differential test of the mise.toml parser against Python's tomllib.

The script writes random documents of four kinds to OUT_DIR, runs
`tomljson` (test/MiseTest/TomlJson.lean) on all of them, and parses each
one with tomllib:

- subset: valid TOML inside the subset mise reads. tomllib must give the
  value the generator meant, and the Lean parser must give the same value.
- outside: valid TOML with one feature mise does not read (dotted keys,
  multi-line strings, floats, other integer forms, dates and times).
  tomllib must accept it, and the Lean parser must reject it with one of
  its "not supported" messages.
- malformed: a subset document with one known error. Both must reject it.
- mutant: a subset document with one to three random character edits.

For every document, if the Lean parser accepts it then tomllib must accept
it with the same value, byte for byte in canonical JSON. If tomllib accepts
a mutant and the Lean parser rejects it, the message must be one of the
"not supported" ones: the parser may read less than TOML, never misread.

usage: toml_diff.py [--seed S] [--tomljson PATH] OUT_DIR N
"""
import argparse
import json
import random
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path

DELIBERATE = (
    "dotted keys are not supported",
    "multi-line strings are not supported",
    "unsupported value",
)

ESC = {"\b": "\\b", "\t": "\\t", "\n": "\\n", "\f": "\\f", "\r": "\\r", '"': '\\"', "\\": "\\\\"}
BARE = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-")
# Replaced by invalid UTF-8 after encoding; the character generator never
# produces it.
SENTINEL = ""


def canon(v):
    return json.dumps(v, sort_keys=True, separators=(",", ":"), default=str)


def is_ctrl(c):
    return (ord(c) < 0x20 and c != "\t") or ord(c) == 0x7F


class Gen:
    def __init__(self, rng):
        self.r = rng

    # Characters and strings

    def char(self):
        r = self.r.random()
        if r < 0.45:
            return chr(self.r.randint(0x20, 0x7E))
        if r < 0.55:
            return self.r.choice("\t\n\r\b\f\"\\'#=[]{},. ")
        if r < 0.62:
            return chr(self.r.choice([*range(0, 0x20), 0x7F]))
        if r < 0.75:
            return chr(self.r.randint(0x80, 0x7FF))
        if r < 0.9:
            while True:
                n = self.r.randint(0x800, 0xFFFF)
                if not 0xD800 <= n <= 0xDFFF and chr(n) != SENTINEL:
                    return chr(n)
        return chr(self.r.randint(0x10000, 0x10FFFF))

    def text(self, lo=0, hi=8):
        return "".join(self.char() for _ in range(self.r.randint(lo, hi)))

    def hexesc(self, c):
        n = ord(c)
        if n <= 0xFFFF and self.r.random() < 0.7:
            h = f"\\u{n:04x}"
        else:
            h = f"\\U{n:08x}"
        return h if self.r.random() < 0.5 else h[:2] + h[2:].upper()

    def basic(self, s):
        out = []
        for c in s:
            if c in ESC and (c not in "\t" or self.r.random() < 0.5):
                out.append(ESC[c] if self.r.random() < 0.8 else self.hexesc(c))
            elif is_ctrl(c) or self.r.random() < 0.1:
                out.append(self.hexesc(c))
            else:
                out.append(c)
        return '"' + "".join(out) + '"'

    @staticmethod
    def literal_ok(s):
        return "'" not in s and not any(is_ctrl(c) for c in s)

    def string(self):
        s = self.text()
        if self.literal_ok(s) and self.r.random() < 0.3:
            return "'" + s + "'", s
        return self.basic(s), s

    def keyname(self):
        r = self.r.random()
        if r < 0.6:
            return "".join(self.r.choice(sorted(BARE)) for _ in range(self.r.randint(1, 6)))
        if r < 0.75:
            return self.r.choice(["true", "false", "inf", "nan", "1", "0x1", "-", "_", "1979-05-27", "a", "b"])
        return self.text(0, 5)

    def key(self, name):
        if name and set(name) <= BARE and self.r.random() < 0.8:
            return name
        if self.literal_ok(name) and self.r.random() < 0.3:
            return "'" + name + "'"
        return self.basic(name)

    def fresh(self, used):
        while True:
            k = self.keyname()
            if k not in used:
                used.add(k)
                return k

    # Whitespace and comments

    def ws(self):
        return self.r.choice(["", "", " ", " ", "  ", "\t", " \t "])

    def comment(self):
        cs = "".join(c for c in self.text(0, 10) if not is_ctrl(c))
        return "#" + cs

    def nl(self):
        return "\r\n" if self.crlf and (self.crlf == 2 or self.r.random() < 0.5) else "\n"

    def gap(self):
        """Whitespace inside an array: spaces, newlines and comments."""
        r = self.r.random()
        if r < 0.5:
            return self.ws()
        if r < 0.8:
            return self.ws() + self.nl() + self.ws()
        return self.ws() + self.comment() + self.nl() + self.ws()

    def trail(self):
        r = self.r.random()
        return self.ws() + (self.comment() if r < 0.25 else "")

    # Values

    def integer(self):
        r = self.r.random()
        if r < 0.15:
            n = 0
        elif r < 0.6:
            n = self.r.randint(-1000, 1000)
        elif r < 0.95:
            n = self.r.randint(-(2**63), 2**63 - 1)
        else:
            n = self.r.randint(-(10**30), 10**30)
        digits = str(abs(n))
        if len(digits) > 1 and self.r.random() < 0.3:
            out = digits[0]
            for d in digits[1:]:
                out += ("_" if self.r.random() < 0.3 else "") + d
            digits = out
        sign = "-" if n < 0 or (n == 0 and self.r.random() < 0.1) else ("+" if self.r.random() < 0.15 else "")
        return sign + digits, n

    def value(self, depth=0):
        kinds = ["str"] * 3 + ["int"] * 2 + ["bool"]
        if depth < 3:
            kinds += ["arr", "tab"]
        k = self.r.choice(kinds)
        if k == "str":
            return self.string()
        if k == "int":
            return self.integer()
        if k == "bool":
            b = self.r.random() < 0.5
            return ("true" if b else "false"), b
        if k == "arr":
            items = [self.value(depth + 1) for _ in range(self.r.randint(0, 4))]
            if not items:
                return "[" + self.r.choice(["", " ", self.gap()]) + "]", []
            body = ""
            for i, (t, _) in enumerate(items):
                body += self.gap() + t + self.gap()
                if i + 1 < len(items) or self.r.random() < 0.3:
                    body += ","
            return "[" + body + self.gap() + "]", [v for _, v in items]
        used = set()
        items = []
        for _ in range(self.r.randint(0, 3)):
            name = self.fresh(used)
            t, v = self.value(depth + 1)
            items.append((self.key(name) + self.ws() + "=" + self.ws() + t, name, v))
        if not items:
            return self.r.choice(["{}", "{ }", "{\t}"]), {}
        body = ("," + self.ws()).join(t + self.ws() for t, _, _ in items)
        return "{" + self.ws() + body + "}", {n: v for _, n, v in items}

    # Documents

    def doc(self):
        """A subset document as regions: the root, then sections. Each
        region has a header line (or None), key-value lines, the keys used,
        and the value it adds."""
        self.crlf = self.r.choice([0, 0, 0, 1, 2])
        value = {}
        root = {"header": None, "lines": [], "used": set(), "names": [], "table": value}
        regions = [root]
        for _ in range(self.r.randint(0, 5)):
            self.kv(root)
        arrays = []
        for _ in range(self.r.randint(0, 5)):
            if arrays and self.r.random() < 0.4:
                name = self.r.choice(arrays)
                self.section(regions, value, name, True)
            elif self.r.random() < 0.4:
                name = self.fresh(root["used"])
                arrays.append(name)
                value[name] = []
                self.section(regions, value, name, True)
            else:
                name = self.fresh(root["used"])
                self.section(regions, value, name, False)
        return regions, value

    def kv(self, region, name=None, text=None, v=None):
        if name is None:
            name = self.fresh(region["used"])
        if text is None:
            text, v = self.value()
        region["lines"].append(self.ws() + self.key(name) + self.ws() + "=" + self.ws() + text + self.trail())
        region["names"].append(name)
        region["table"][name] = v

    def header(self, name, arr):
        o, c = ("[[", "]]") if arr else ("[", "]")
        return self.ws() + o + self.ws() + self.key(name) + self.ws() + c + self.trail()

    def section(self, regions, value, name, arr):
        t = {}
        if arr:
            value[name].append(t)
        else:
            value[name] = t
        reg = {"header": self.header(name, arr), "lines": [], "used": set(), "names": [], "table": t, "name": name}
        regions.append(reg)
        for _ in range(self.r.randint(0, 4)):
            self.kv(reg)

    def render(self, regions):
        out = []
        for reg in regions:
            if reg["header"] is not None:
                out.append(reg["header"])
            for line in reg["lines"]:
                while self.r.random() < 0.15:
                    out.append(self.r.choice(["", self.ws(), self.ws() + self.comment()]))
                out.append(line)
        text = self.nl().join(out)
        if self.r.random() < 0.8:
            text += self.nl()
        if self.r.random() < 0.1:
            text = self.nl() + text
        return text

    # Outside the subset: one valid feature mise does not read.

    OUTSIDE_VALUES = {
        "float": ["1.5", "-0.0", "+1e3", "3.141_59", "6.626e-34", "1E6", "inf", "-inf", "+nan", "nan", "0.0"],
        "radix": ["0xdead_beef", "0xDEADBEEF", "0x0", "0o755", "0o0", "0b1101", "0b0"],
        "datetime": ["1979-05-27T07:32:00Z", "1979-05-27 07:32:00-07:00", "1979-05-27T00:32:00.999999",
                     "1979-05-27t07:32:00z", "1979-05-27", "07:32:00", "00:32:00.5"],
        "ml-basic": ['"""\nfoo\nbar"""', '"""a"b"""', '""""""', '"""\\\n   x"""', '"""é\\u00e9"""'],
        "ml-literal": ["'''\nx\n'''", "'''a'b'''", "''''''"],
    }

    def wrap(self, t):
        r = self.r.random()
        if r < 0.6:
            return t
        if r < 0.8:
            return "[" + self.value(2)[0] + ", " + t + "]"
        return "{ " + self.key(self.keyname()) + " = " + t + " }"

    def outside(self):
        regions, _ = self.doc()
        tag = self.r.choice(list(self.OUTSIDE_VALUES) + ["dotted-key", "dotted-inline", "dotted-header"])
        reg = self.r.choice(regions)
        if tag in self.OUTSIDE_VALUES:
            self.insert(reg, self.wrap(self.r.choice(self.OUTSIDE_VALUES[tag])))
        elif tag == "dotted-key":
            a = self.fresh(reg["used"])
            line = self.key(a) + self.ws() + "." + self.ws() + self.key(self.keyname()) + " = " + self.value()[0]
            reg["lines"].insert(self.r.randint(0, len(reg["lines"])), line)
        elif tag == "dotted-inline":
            self.insert(reg, "{ " + self.key("a") + "." + self.key("b") + " = 1 }")
        else:
            a = self.fresh(regions[0]["used"])
            regions.append({"header": "[" + self.key(a) + "." + self.key(self.keyname()) + "]",
                            "lines": [], "used": set(), "names": [], "table": {}})
        return tag, self.render(regions)

    def insert(self, reg, text, name=None, trail=True):
        """Insert `name = text` at a random place in a region."""
        if name is None:
            name = self.fresh(reg["used"])
        line = self.ws() + self.key(name) + self.ws() + "=" + self.ws() + text + (self.trail() if trail else "")
        reg["lines"].insert(self.r.randint(0, len(reg["lines"])), line)

    # Malformed: one known error.

    BAD_VALUES = {
        "unterminated": ['"abc', "'abc", '"abc\\"', '"\\'],
        "newline-in-string": ['"a\nb"', "'a\nb'"],
        "bad-escape": ['"\\q"', '"\\e"', '"\\x41"', '"\\ "', '"\\u12"', '"\\uD800"', '"\\udfff"',
                       '"\\U00110000"', '"\\U0000004"', '"\\U"'],
        "bad-int": ["012", "+_1", "1__0", "1_", "_1", "--1", "+-1", "00", "-01", "1_000_", "0_0"],
        "bad-inline": ["{a=1,}", "{a=1,\nb=2}", "{a=}", "{a 1}", "{,}", "{a=1", "{\n}", "{a=1 b=2}"],
        "bad-array": ["[1 2]", "[,1]", "[1,,2]", "[", "[1,", "[1}", "[,]"],
        "bad-word": ["True", "FALSE", "true1", "tru", "yes", "'x' 'y'", "1 = 2", "\"a\"b", "$"],
        "dup-inline": ["{ a = 1, a = 2 }", "{ a = 1, \"a\" = 2 }", "{ 'a' = 1, b = {}, a = [] }"],
    }

    def malformed(self):
        regions, value = self.doc()
        tags = list(self.BAD_VALUES) + ["ctrl-in-string", "ctrl-in-comment", "dup-key", "redefine",
                                        "bad-statement", "bad-header", "bad-utf8", "bad-space", "lone-cr"]
        tag = self.r.choice(tags)
        reg = self.r.choice(regions)
        if tag == "unterminated":
            # Nothing after it on the line, so no later quote closes it.
            self.insert(reg, self.r.choice(self.BAD_VALUES[tag]), trail=False)
        elif tag in self.BAD_VALUES:
            self.insert(reg, self.wrap(self.r.choice(self.BAD_VALUES[tag])))
        elif tag == "ctrl-in-string":
            c = chr(self.r.choice([*range(0, 9), *range(0x0A, 0x20), 0x7F]))
            q = self.r.choice("\"'")
            self.insert(reg, self.wrap(q + self.text(0, 3).replace(q, "") .replace("\\", "") + c + q))
        elif tag == "ctrl-in-comment":
            c = chr(self.r.choice([*range(0, 9), 0x0B, 0x0C, *range(0x0E, 0x20), 0x7F, 0x0D]))
            line = self.ws() + "#" + "".join(ch for ch in self.text(0, 4) if not is_ctrl(ch)) + c + "x"
            if self.r.random() < 0.5 and reg["lines"]:
                i = self.r.randrange(len(reg["lines"]))
                reg["lines"][i] += " " + line.strip()
            else:
                reg["lines"].insert(self.r.randint(0, len(reg["lines"])), line)
        elif tag == "dup-key":
            if not reg["names"]:
                self.kv(reg)
            name = self.r.choice(reg["names"])
            self.insert(reg, self.value()[0], name=name)
        elif tag == "redefine":
            self.redefine(regions, value)
        elif tag == "bad-statement":
            line = self.r.choice(["a =", "a 1", "a = 1 b = 2", "= 1", "a$b = 1", "é = 1", "a b = 1",
                                  "a = 1,", "a == 1", "a = 1 # c\n= 2", "\"a\" \"b\" = 1", "a=1]"])
            reg["lines"].insert(self.r.randint(0, len(reg["lines"])), line.replace("a", self.key(self.fresh(reg["used"])), 1)
                                if self.r.random() < 0.5 and not line.startswith("a$") else line)
        elif tag == "bad-header":
            n = self.fresh(regions[0]["used"])
            h = self.r.choice(["[{}", "[[{}]", "[{}]]", "[ [{}]]", "[]", "[[]]", "[{}] b = 1", "[{}] x",
                               "[[{}] ]", "[ {} ", "[{}]\t\t[x]"]).replace("{}", self.key(n))
            regions.append({"header": h, "lines": [], "used": set(), "names": [], "table": {}})
        elif tag == "bad-utf8":
            self.insert(reg, self.wrap('"a' + SENTINEL + 'b"') if self.r.random() < 0.6 else "1 #" + SENTINEL)
        elif tag == "bad-space":
            sp = self.r.choice([" ", "　", " ", "\x0c", "\x0b", "﻿"])
            name = self.key(self.fresh(reg["used"]))
            line = self.r.choice([sp + name + " = 1", name + sp + "= 1", name + " =" + sp + "1",
                                  name + " = [1," + sp + "2]", name + " = {" + sp + "}"])
            reg["lines"].insert(self.r.randint(0, len(reg["lines"])), line)
        else:  # lone-cr
            if not reg["lines"]:
                self.kv(reg)
            i = self.r.randrange(len(reg["lines"]))
            reg["lines"][i] += "\r" + self.ws() + self.key(self.fresh(reg["used"])) + " = 1"
        text = self.render(regions)
        if tag == "bad-utf8":
            bad = self.r.choice([b"\xff", b"\xe2\x82", b"\xc0\xaf", b"\xed\xa0\x80", b"\x80", b"\xf4\x90\x80\x80"])
            return tag, text.encode().replace(SENTINEL.encode(), bad)
        return tag, text.encode()

    def redefine(self, regions, value):
        root = regions[0]
        n = self.fresh(root["used"])
        k = self.key(n)
        form = self.r.choice(["tt", "kt", "kA", "At", "tA", "it"])
        first, second = {
            "tt": ("[{}]", "[{}]"), "kt": (None, "[{}]"), "kA": (None, "[[{}]]"),
            "At": ("[[{}]]", "[{}]"), "tA": ("[{}]", "[[{}]]"), "it": (None, "[{}]"),
        }[form]
        if first is None:
            self.insert(root, {"kt": "1", "kA": "[]", "it": "{}"}[form], name=n)
        else:
            regions.append({"header": first.format(k), "lines": [], "used": set(), "names": [], "table": {}})
        others = [regions.pop() for _ in range(self.r.randint(0, len(regions) - 1) if len(regions) > 1 and first is None else 0)]
        regions.extend(reversed(others))
        regions.append({"header": second.format(self.key(n)), "lines": [], "used": set(), "names": [], "table": {}})

    # Mutants: random character edits.

    MUT_CHARS = "[]{}=,.\"'#\\ \t\n\r_-+0123456789abexuUtrf:"

    def mutant(self):
        regions, _ = self.doc()
        s = list(self.render(regions))
        for _ in range(self.r.randint(1, 3)):
            op = self.r.choice(["del", "ins", "rep", "dup"])
            i = self.r.randint(0, len(s))
            if op == "ins" or not s:
                s.insert(i, self.r.choice(self.MUT_CHARS) if self.r.random() < 0.9 else self.char())
            elif i < len(s) and op == "del":
                del s[i]
            elif i < len(s) and op == "rep":
                s[i] = self.r.choice(self.MUT_CHARS)
            elif i < len(s):
                s.insert(i, s[i])
        return "mutant", "".join(s).encode()


def tomllib_result(data):
    try:
        return True, tomllib.loads(data.decode("utf-8"))
    except (tomllib.TOMLDecodeError, UnicodeDecodeError) as e:
        return False, str(e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--tomljson", default=".lake/build/bin/tomljson")
    ap.add_argument("out", type=Path)
    ap.add_argument("n", type=int)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    g = Gen(rng)
    shutil.rmtree(a.out, ignore_errors=True)
    a.out.mkdir(parents=True)
    cases = []  # (path, kind, tag, data, expected value or None)
    for kind in ["subset", "outside", "malformed", "mutant"]:
        for i in range(a.n):
            if kind == "subset":
                regions, v = g.doc()
                tag, data, expect = "subset", g.render(regions).encode(), v
            else:
                tag, data = getattr(g, kind)()
                if isinstance(data, str):
                    data = data.encode()
                expect = None
            p = a.out / f"{kind}-{i:05d}.toml"
            p.write_bytes(data)
            cases.append((p, kind, tag, data, expect))

    lean = []
    paths = [str(c[0]) for c in cases]
    for i in range(0, len(paths), 500):
        out = subprocess.run([a.tomljson, *paths[i:i + 500]], check=True, capture_output=True, text=True).stdout
        lean += out.splitlines()
    assert len(lean) == len(cases)

    fails = 0
    why_count = {}
    tags = {}
    lean_ok = {}

    def fail(p, kind, tag, why, lr, tr):
        nonlocal fails
        fails += 1
        why_count[(kind, tag, why)] = why_count.get((kind, tag, why), 0) + 1
        if fails <= 20:
            print(f"FAIL {p} ({kind}/{tag}): {why}\n  lean:    {lr[:300]}\n  tomllib: {str(tr)[:300]}")

    for (p, kind, tag, data, expect), lr in zip(cases, lean):
        tags.setdefault(kind, {}).setdefault(tag, 0)
        tags[kind][tag] += 1
        tok, tv = tomllib_result(data)
        lok = lr.startswith("ok ")
        lean_ok[kind] = lean_ok.get(kind, 0) + lok
        tr = canon(tv) if tok else "error: " + tv
        if lok and (not tok or canon(tv) != lr[3:]):
            fail(p, kind, tag, "the Lean parser accepts and disagrees with tomllib", lr, tr)
        elif kind == "subset":
            if not tok or canon(tv) != canon(expect):
                fail(p, kind, tag, "generator bug: tomllib does not read the intended value", canon(expect), tr)
            elif not lok:
                fail(p, kind, tag, "the Lean parser rejects a document in the subset", lr, tr)
        elif kind == "outside":
            if not tok:
                fail(p, kind, tag, "generator bug: tomllib rejects a document outside the subset", lr, tr)
            elif lok or not any(m in lr for m in DELIBERATE):
                fail(p, kind, tag, "the Lean parser does not reject with a 'not supported' message", lr, tr)
        elif kind == "malformed":
            if tok:
                fail(p, kind, tag, "generator bug: tomllib accepts a malformed document", lr, tr)
            elif lok:
                fail(p, kind, tag, "the Lean parser accepts a malformed document", lr, tr)
        elif tok and not lok and not any(m in lr for m in DELIBERATE):
            fail(p, kind, tag, "the Lean parser rejects valid TOML outside its 'not supported' cases", lr, tr)

    total = len(cases)
    if fails:
        for (kind, tag, why), c in sorted(why_count.items()):
            print(f"  {c} x {kind}/{tag}: {why}")
        print(f"toml-diff: {fails} of {total} documents failed")
        return 1
    mut_ok = lean_ok.get("mutant", 0)
    print(f"toml-diff: {total} documents agree with tomllib ({sys.version.split()[0]}): "
          f"{a.n} in the subset, {a.n} outside it ({len(tags['outside'])} features), "
          f"{a.n} malformed ({len(tags['malformed'])} kinds), {a.n} mutants ({mut_ok} accepted by both)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
