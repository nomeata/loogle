{
  inputs.lean.url = github:leanprover/lean4/b5a736708f40;

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.nixpkgs.follows = "lean/nixpkgs";

  inputs.mathlib4.url = "github:leanprover-community/mathlib4/joachim/find-no-ProofWidgets";
  #inputs.mathlib4.url = "git+file:///home/jojo/build/lean/mathlib4?rev=069e0083ff4f1081710a73ec243e66d659ae59d5";
  #inputs.mathlib4.url = "github:leanprover-community/mathlib4/joachim/find";
  inputs.mathlib4.flake = false;
  inputs.std4.url = "github:leanprover/std4/8b864260672b21d964d79ecb2376e01d0eab9f5b";
  inputs.std4.flake = false;
  inputs.quote4.url = "github:gebner/quote4/81cc13c524a68d0072561dbac276cd61b65872a6";
  inputs.quote4.flake = false;
  inputs.aesop.url = "github:nomeata/JLimpberg/d13a9666e6f430b940ef8d092f1219e964b52a09";
  inputs.aesop.flake = false;
  inputs.ProofWidgets.url = "github:EdAyers/ProofWidgets4/a0c2cd0ac3245a0dade4f925bcfa97e06dd84229";
  inputs.ProofWidgets.flake = false;
  outputs = { self, nixpkgs, ...}@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};

      std4 = inputs.lean.packages.${system}.buildLeanPackage {
        name = "Std";
        src = inputs.std4;
        roots = [ { mod = "Std"; glob = "one"; } ];
      };

      quote4 = inputs.lean.packages.${system}.buildLeanPackage {
        name = "Qq";
        src = inputs.quote4;
        roots = [ { mod = "Qq"; glob = "one"; } ];
      };

      aesop = inputs.lean.packages.${system}.buildLeanPackage {
        name = "Aesop";
        src = inputs.aesop;
        roots = [ "Aesop" ];
        deps = [std4];
      };

      # ProofWidgets_flake = lake2nix.lib.lakeRepo2flake {
      #   name = "ProofWidgets";
      #   lean = lake2nix.inputs.lean;
      #   src = inputs.ProofWidgets;
      #   depFlakes = [std4_flake];
      # };

      mathlib4 = inputs.lean.packages.${system}.buildLeanPackage {
        name = "Mathlib";
        src = inputs.mathlib4;
        roots = [ { mod = "Mathlib"; glob = "one"; } ];
        leanFlags = [
          "-Dpp.unicode.fun=true"
          "-DautoImplicit=false"
          "-DrelaxedAutoImplicit=false"
        ];
        deps = [std4 quote4 aesop];
      };

      loogle = inputs.lean.packages.${system}.buildLeanPackage {
        name = "loogle";
        src = ./.;
        roots = [ "Loogle" ];
        deps = [ mathlib4 ];
        # hack = true;
      };
    in
    {
      packages.${system} = {
        loogle = loogle.executable;
      };

      devShells.${system}.default = (pkgs.mkShell.override { stdenv = pkgs.llvmPackages_15.stdenv; }) {
        packages = with pkgs;
          [ elan
            pkgsStatic.libseccomp
            pkgconfig
            python3
          ];
      };
    };
}
