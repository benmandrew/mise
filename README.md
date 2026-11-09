# mise

`mise` is a Lean 4 front end for [Ninja](https://ninja-build.org/). A build is described in a `mise.toml` file, `mise` emits `build.ninja` from it, and proofs show that the emitted build is correct and incrementally sound relative to an abstract model of Ninja 1.13.

Dependencies come from the Nix flake: Lean, Ninja, Python and a C compiler, pinned by `flake.lock`. Enter the shell, then build and run an example:

```sh
nix develop    # or `direnv allow` once, to load it on entering the directory
lake build
mise build examples/hello-c   # reads mise.toml, writes build.ninja, runs ninja
```

- [Usage](docs/usage.md): the `mise` command and the `mise.toml` format.
- [Theorems](docs/theorems.md): what is proved, by stage.
- [Trust base](docs/trust.md): what is assumed, and the supported Ninja subset.
- [Testing](docs/testing.md): the acceptance gate and the tests against real Ninja.
