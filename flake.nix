{
  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.lean.url = github:leanprover/lean4/b5a736708f40;
  inputs.lake2nix.url = "github:Kha/nale?dir=lake2nix";
  inputs.lake2nix.inputs.lean.follows = "lean";

  inputs.mathlib4.url = "github:leanprover-community/mathlib4/joachim/find-no-ProofWidgets";
  #inputs.mathlib4.url = "git+file:///home/jojo/build/lean/mathlib4?rev=069e0083ff4f1081710a73ec243e66d659ae59d5";
  #inputs.mathlib4.url = "github:leanprover-community/mathlib4/joachim/find";
  inputs.mathlib4.flake = false;
  inputs.std4.url = "github:leanprover/std4/8b864260672b21d964d79ecb2376e01d0eab9f5b";
  inputs.std4.flake = false;
  inputs.quote4.url = "github:gebner/quote4/81cc13c524a68d0072561dbac276cd61b65872a6";
  inputs.quote4.flake = false;
  inputs.aesop.url = "github:JLimperg/aesop/d13a9666e6f430b940ef8d092f1219e964b52a09";
  inputs.aesop.flake = false;
  inputs.ProofWidgets.url = "github:EdAyers/ProofWidgets4/a0c2cd0ac3245a0dade4f925bcfa97e06dd84229";
  inputs.ProofWidgets.flake = false;
  outputs = { self, nixpkgs, lake2nix, ...}@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};

      std4_flake = lake2nix.lib.lakeRepo2flake {
        name = "std4";
        lean = lake2nix.inputs.lean;
        src = inputs.std4;
        depFlakes = [];
      };

      quote4_flake = lake2nix.lib.lakeRepo2flake {
        name = "quote4";
        lean = lake2nix.inputs.lean;
        src = inputs.quote4;
        depFlakes = [];
      };

      aesop_flake = lake2nix.lib.lakeRepo2flake {
        name = "aesop";
        lean = lake2nix.inputs.lean;
        src = inputs.aesop;
        depFlakes = [std4_flake];
      };

      ProofWidgets_flake = lake2nix.lib.lakeRepo2flake {
        name = "ProofWidgets";
        lean = lake2nix.inputs.lean;
        src = inputs.ProofWidgets;
        depFlakes = [std4_flake];
      };


      mathlib4_flake = lake2nix.lib.lakeRepo2flake {
        name = "mathlib4";
        lean = lake2nix.inputs.lean;
        src = inputs.mathlib4;
        depFlakes = [std4_flake quote4_flake aesop_flake];
      };

      loogle_flake = lake2nix.lib.lakeRepo2flake {
        name = "loogle";
        lean = lake2nix.inputs.lean;
        src = ./.;
        depFlakes = [mathlib4_flake std4_flake quote4_flake aesop_flake ];
      };

      loogle = inputs.lean.packages.${system}.buildLeanPackage {
      #loogle = lake2nix.inputs.lean.packages.${system}.buildLeanPackage {
        name = "loogle";
        src = ./.;
        roots = [ "Loogle" ];
        deps = nixpkgs.lib.unique (builtins.concatMap (d: d.packages.${system}.deps) [mathlib4_flake std4_flake quote4_flake aesop_flake ]);
      };
    in
    {
      packages.${system} = {
        std4 = std4_flake.packages.${system}.Std;
        mathlib4 = mathlib4_flake.packages.${system}.Mathlib;
        loogle = loogle;
        loogleLib = loogle.modRoot;
      };

      # doesn't work yet, need to package dependencies and think about
      # (or ditch) alloy
      #packages.${system} = lakePkg;

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
