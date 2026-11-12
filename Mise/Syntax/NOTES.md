# Stage 3 notes: Ninja syntax, printer, parser model, round trip

Tested against Ninja `1.13.2` (Homebrew, macOS arm64).

## Definitions

- `Ast.lean`: `Path` (a `String`), `Seg` and `EvalString` (literal text and `${var}` references), `Rule`, `Edge`, `Stmt` and `Manifest`, a statement list that keeps the order of rules, edges and top-level bindings.
- `Print.lean`: the printer, over `List Char`. Paths escape `$`, space and `:`; values escape `$` and a leading space; references print as `${name}`.
- `Parse.lean`: the *parser model*, one statement per header line plus its indented block, lexing as `ReadIdent`, `ReadPath` and `ReadVarValue` do in Ninja's `lexer.in.re`.
- `RoundTrip.lean`: the proof, plus `unescapePath`.

`Manifest.WellFormed m` means every statement passes `Stmt.ok` in the context (`Ctx`) of the statements before it. The parser model runs the same `Stmt.ok`, so both share one definition. It covers these conditions:

- identifiers, literals and paths use only characters Ninja can lex, and literals are never adjacent;
- paths are canonical, so `CanonicalizePath` leaves them unchanged;
- top-level variable names are not keywords, and no top-level or edge variable is `pool` or `dyndep` (`parseTimeKeys`);
- rule names are new and not `phony`, rule keys are in the supported subset, and the last `command` binding is nonempty;
- an edge's rule is defined earlier, and it has at least one explicit output, with outputs distinct, not produced by an earlier edge and not among its own inputs;
- `default` targets are nonempty and each was mentioned by an earlier edge.

## Theorems

- `parse_print`: `parse (print m) = some m` for every well-formed `m`.
- `unescape_escPath`: `unescapePath (escPath p) = some p` for valid `p`.
- `unescape_renderVal`: `readValue (renderVal e) = some e` for valid `e`.

None of `RoundTrip.lean` duplicates Mathlib, so the plan's Mathlib threshold does not apply.

## Deviations from the plan

- `Path` is a plain `String` with validity in `WellFormed`, which keeps keys simple for Stages 4 and 5.
- `WellFormed` includes context checks (unique outputs, known `default` targets, a nonempty last `command`) because Ninja rejects these at parse time.

## Where the parser model differs from Ninja

The model agrees with Ninja on every input it accepts. It rejects some inputs Ninja accepts:

- `$`-newline continuations and `\r\n` line endings;
- variable references inside paths;
- non-canonical paths;
- `pool`, `include`, `subninja`, `|@` validations, and rule keys outside the subset such as `rspfile`;
- `pool` and `dyndep` as variables (`parseTimeKeys`), which Ninja reads while it parses an edge.

The model does not evaluate variables, and accepts any `deps` value because Ninja checks it only at build time.

The differential test found two behaviours that are now modelled: Ninja rejects an empty last `command` binding but accepts `${v}` with an empty `v`, and `-t query` lists a consuming edge once per occurrence of an input. The parser fuzzer (`fuzz/fuzz.sh parser`) found four more, all accepted by the model before. Ninja rejects a nonempty manifest whose last line has no newline. It reads a NUL byte in a comment as the end of the input. It rejects an edge whose `pool` variable names no declared pool. It drops a phony edge's own output from its inputs.

## Tests

`test/stage3-diff.sh` is the differential test against `ninja -t query`; see `docs/testing.md`.
