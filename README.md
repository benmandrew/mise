# mise

`mise` is a Lean 4 front end for [Ninja](https://ninja-build.org/). A build is described in Lean, `mise` emits `build.ninja`, and proofs show that the emitted build is correct and incrementally sound relative to an abstract model of Ninja 1.13.

```sh
lake build
lake exe gen examples/hello-c
ninja -C examples/hello-c
```

- [Usage](docs/usage.md): the `gen` command and the DSL.
- [Theorems](docs/theorems.md): what is proved, by stage.
- [Trust base](docs/trust.md): what is assumed, and the supported Ninja subset.
- [Testing](docs/testing.md): the acceptance gate and the tests against real Ninja.
