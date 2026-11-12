{
  description = "mise: a Lean 4 front end for Ninja";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "aarch64-darwin" "x86_64-darwin" "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      lib = nixpkgs.lib;

      # Ninja releases for the conformance matrix (test/ninja-matrix.sh), as
      # packages `ninja-1_10_2` and so on and shells of the same names. The
      # default shell keeps nixpkgs' Ninja.
      ninjaReleases = {
        "1.10.2" = "sha256-pfy7MApC5OvY+mxo1Ax3r3T7hxePfrFFzDiQvivBV1c=";
        "1.11.1" = "sha256-LvV/Fi2ARXBkfyA1paCRmLUwCh/rTyz+tGMg2/qEepI=";
        "1.12.1" = "sha256-RT5u+TDvWxG5EVQEYj931EZyrHUSAqK73OKDAascAwA=";
        "1.13.2" = "sha256-D9HsIjv8EJ1qAdXFAKy260K77cCvopgQ2Fx6uXpt6VI=";
      };
      attrName = v: "ninja-" + builtins.replaceStrings [ "." ] [ "_" ] v;

      # Each release is built from its upstream tag. nixpkgs' own patch (spawn
      # `sh` from PATH) is dropped, so the binary is the release as published;
      # releases before 1.12 get the upstream fix that lets configure.py run on
      # Python 3.13.
      ninjaAt = pkgs: version: hash:
        (pkgs.ninja.override { buildDocs = false; }).overrideAttrs (old: {
          inherit version;
          src = pkgs.fetchFromGitHub {
            owner = "ninja-build";
            repo = "ninja";
            tag = "v${version}";
            inherit hash;
          };
          patches = lib.optionals (lib.versionOlder version "1.12") [
            (pkgs.fetchpatch {
              name = "ninja-python3.13-compat.patch";
              url = "https://github.com/ninja-build/ninja/commit/9cf13cd1ecb7ae649394f4133d121a01e191560b.patch";
              hash = "sha256-zlMs9LDJ2thtiSUjbsONyqoyYxrB/Ilt2Ljr0nCU6nQ=";
            })
          ];
        });
      ninjas = pkgs: lib.mapAttrs' (v: h: lib.nameValuePair (attrName v) (ninjaAt pkgs v h)) ninjaReleases;

      shellWith = pkgs: ninja: pkgs.mkShell {
        packages = [ pkgs.lean4 ninja pkgs.python3 pkgs.ccache pkgs.typst ];
        # ccache is for the property harness, typst for docs/headline.pdf.
        # `mise` is on PATH after `lake build`.
        shellHook = ''
          export PATH="$PWD/.lake/build/bin:$PATH"
        '';
      };
    in {
      packages = forAll ninjas;

      devShells = forAll (pkgs:
        let
          # Lean comes from nixpkgs; `lean-toolchain` must name the same version.
          toolchain = lib.trim (builtins.readFile ./lean-toolchain);
          wanted = "leanprover/lean4:v${pkgs.lean4.version}";
        in
        assert lib.assertMsg (toolchain == wanted)
          "lean-toolchain says ${toolchain}, but nixpkgs provides ${wanted}";
        # mkShell's stdenv supplies the C compiler the examples use.
        {
          default = shellWith pkgs pkgs.ninja;
          # The fuzzers in fuzz/: clang with libFuzzer, AFL++ on Linux, and
          # the Ninja sources fuzz/build.sh links by default.
          fuzz = (shellWith pkgs pkgs.ninja).overrideAttrs (old: {
            nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ pkgs.clang ]
              ++ lib.optionals pkgs.stdenv.hostPlatform.isLinux [ pkgs.aflplusplus ];
            NINJA_SRC = (ninjas pkgs).ninja-1_13_2.src;
          });
        }
        // lib.mapAttrs (_: shellWith pkgs) (ninjas pkgs));
    };
}
