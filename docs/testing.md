# Testing

Run the tests in the Nix shell (`nix develop`, or direnv with `.envrc`), so that they use the Ninja, Python and compiler pinned by `flake.lock`.

- `scripts/check.sh` is the acceptance gate: it builds everything, rejects `sorry` and `admit`, and checks the axioms of every headline theorem. The Lean tests in `test/MiseTest/` are `#guard` checks that run during the build.
- `test/stage3-diff.sh` compares the parser and evaluation models with real Ninja on 100 random manifests, and checks that both reject 17 malformed ones.
- `test/stage4-hello.sh` builds and runs `examples/hello-c`, and checks that the DSL's commands match `ninja -t commands`.
- `test/stage6-props.sh` runs 200 random edit sequences on each example, building after each edit with a random `-j` level. After every build it compares the products with a clean build byte for byte, and checks that `ninja -n` has no work and `ninja -t missingdeps` finds nothing. After a comment-only edit to `config.in` it checks that only the generator ran. With seed 1 it ran 680 edits on `hello-c` and 710 on `gen-header` in about 5 minutes, and every check passed.

Shell tests write to `test/out/`.
