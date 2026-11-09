{
  description = "mise: a Lean 4 front end for Ninja";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "aarch64-darwin" "x86_64-darwin" "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      devShells = forAll (pkgs:
        let
          # Lean comes from nixpkgs; `lean-toolchain` must name the same version.
          toolchain = nixpkgs.lib.trim (builtins.readFile ./lean-toolchain);
          wanted = "leanprover/lean4:v${pkgs.lean4.version}";
        in
        assert nixpkgs.lib.assertMsg (toolchain == wanted)
          "lean-toolchain says ${toolchain}, but nixpkgs provides ${wanted}";
        {
          # mkShell's stdenv supplies the C compiler the examples use.
          default = pkgs.mkShell {
            packages = [ pkgs.lean4 pkgs.ninja pkgs.python3 ];
            # `mise` is on PATH after `lake build`.
            shellHook = ''
              export PATH="$PWD/.lake/build/bin:$PATH"
            '';
          };
        });
    };
}
