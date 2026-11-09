# Stage 3 notes: Ninja syntax, printer, parser model, round trip

Tested against Ninja `1.13.2` (Homebrew, macOS arm64).

## Definitions

- `Ast.lean`: `Path` (a `String`), `Seg` and `EvalString` (literal text and `${var}` references), `Rule`, `Edge`, `Stmt` and `Manifest`. A manifest is a statement list, so the order of rules, edges and top-level bindings is kept.
- `Print.lean`: the printer works on `List Char`. Paths escape `$`, space and `:`. Values escape `$`, plus a leading space as `$ ` because Ninja skips spaces after `=`. Variable references always print as `${name}`. Rule blocks end with a blank line; edges do not.
- `Parse.lean`: the parser model. It splits the input into lines, classifies each line (blank, comment, indented, top), and parses one statement per header line plus its indented block. Line lexing follows Ninja's `lexer.in.re`: `ReadIdent`, `ReadPath` and `ReadVarValue`, with spaces eaten after each token.
- `RoundTrip.lean`: the proof, plus `unescapePath`.

## Well-formedness

`Manifest.WellFormed m` means every statement passes `Stmt.ok` in the context (`Ctx`) of the statements before it. The parser model runs the same `Stmt.ok` on every statement it reads, so "well formed" and "accepted by the parser model's checks" share one definition. `Stmt.ok` covers the syntactic conditions from the plan and the parse-time errors real Ninja raises:

- identifiers, literals and paths use only characters Ninja can lex, and literals are never adjacent (the parser merges them);
- paths are canonical, so Ninja's `CanonicalizePath` leaves them unchanged;
- top-level variable names are not keywords;
- rule names are new and not `phony`; rule keys are in the supported subset; the last `command` binding is nonempty;
- an edge's rule is defined earlier; it has at least one explicit output; its outputs are distinct and not produced by an earlier edge;
- `default` targets are nonempty and each was mentioned by an earlier edge.

## Theorems

- `parse_print`: `parse (print m) = some m` for every well-formed `m`.
- `unescape_escPath`: `unescapePath (escPath p) = some p` for valid `p`.
- `unescape_renderVal`: `readValue (renderVal e) = some e` for valid `e`.

`RoundTrip.lean` is 925 lines. None of it duplicates Mathlib; the lemmas are about this parser's functions, so the Mathlib threshold in the plan does not apply.

## Deviations from the plan

- `Path` is a plain `String`, and validity lives in `WellFormed`, where the plan suggests a validated string type. This keeps keys simple for Stages 4 and 5.
- `WellFormed` includes context checks (unique outputs, known `default` targets, an empty last `command`) because real Ninja rejects these at parse time. Each was confirmed by a negative test.

## Where the parser model differs from real Ninja

The model is meant to agree with Ninja on every input it accepts. It rejects some inputs Ninja accepts:

- `$`-newline line continuations and `\r\n` line endings;
- variable references inside paths (Ninja expands them);
- non-canonical paths (Ninja canonicalises them);
- `pool`, `include`, `subninja`, `|@` validations, and rule keys outside the subset such as `pool` and `rspfile`.

The model does not evaluate variables. `deps` values other than `gcc` are accepted, as Ninja only checks them at build time.

## Tests

`test/stage3-diff.sh [N] [SEED]` runs `lake exe difftest`, which writes `N` random well-formed manifests with paths built from components such as `x y`, `d$e`, `f:g`, ` lead`, `ü` and `日本`. For every path in each manifest it computes the expected `ninja -t query` output from the AST, and the script compares that with real Ninja. It also writes 17 hand-written manifests that the parser model rejects, and checks that Ninja rejects each one.

Results: seed 1 with 100 manifests and seed 7 with 300 manifests both agree, and Ninja rejects all 17 negative cases.

The test found two things that are now modelled. Ninja rejects a rule whose last `command` binding is empty, though `${v}` with an empty `v` is accepted. And `-t query` lists a consuming edge once per occurrence of the input, so an input repeated in one edge appears twice.
