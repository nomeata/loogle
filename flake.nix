{
  inputs.lean.url = github:leanprover/lean4/b5a736708f40;

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.nixpkgs.follows = "lean/nixpkgs";

  inputs.mathlib4.url = "github:leanprover-community/mathlib4/joachim/find-no-ProofWidgets";
  inputs.mathlib4.flake = false;
  inputs.std4.url = "github:leanprover/std4/8b864260672b21d964d79ecb2376e01d0eab9f5b";
  inputs.std4.flake = false;
  inputs.quote4.url = "github:gebner/quote4/81cc13c524a68d0072561dbac276cd61b65872a6";
  inputs.quote4.flake = false;
  inputs.aesop.url = "github:JLimperg/aesop/d13a9666e6f430b940ef8d092f1219e964b52a09";
  inputs.aesop.flake = false;

  # inputs.ProofWidgets.url = "github:EdAyers/ProofWidgets4/a0c2cd0ac3245a0dade4f925bcfa97e06dd84229";
  # inputs.ProofWidgets.flake = false;

  outputs = { self, nixpkgs, ...}@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      leanPkgs = inputs.lean.packages.${system};

      std4 = leanPkgs.buildLeanPackage {
        name = "Std";
        src = inputs.std4;
        roots = [ { mod = "Std"; glob = "one"; } ];
      };

      quote4 = leanPkgs.buildLeanPackage {
        name = "Qq";
        src = inputs.quote4;
        roots = [ { mod = "Qq"; glob = "one"; } ];
      };

      aesop = leanPkgs.buildLeanPackage {
        name = "Aesop";
        src = inputs.aesop;
        roots = [ "Aesop" ];
        deps = [std4];
      };

      # ProofWidgets = leanPkgs.buildLeanPackage {
      #   name = "ProofWidgets";
      #   src = inputs.ProofWidgets;
      #   roots = [ "ProofWidgets" ];
      #   deps = [std4];
      # };

      mathlib4 = leanPkgs.buildLeanPackage {
        name = "Mathlib";
        src = inputs.mathlib4;
        # src = builtins.fetchTree {
        #   name = "mathlib4-patched";
        #   src = inputs.mathlib4;
        #   postPatch = ''
        #     sed -i '/Widget/d' ./Mathlib.lean ./Mathlib/Tactic.lean
        #   '';
        # };
        roots = [ { mod = "Mathlib"; glob = "one"; } ];
        leanFlags = [
          "-Dpp.unicode.fun=true"
          "-DautoImplicit=false"
          "-DrelaxedAutoImplicit=false"
        ];
        deps = [std4 quote4 aesop ];
      };

      loogle_seccomp = pkgs.runCommandCC "loogle_seccomp"
        { buildInputs = [ leanPkgs.leanc pkgs.pkgsStatic.libseccomp ]; } ''
        mkdir -p $out
        leanc -c -o $out/loogle_seccomp.o ${./loogle_seccomp.c} -fPIC
        ar Trcs $out/loogle_seccomp.a $out/loogle_seccomp.o
      '';

      seccomp = leanPkgs.buildLeanPackage {
        name = "Seccomp";
        src = ./.;
        roots = [ "Seccomp" ];
        deps = leanPkgs.stdlib;
        staticLibDeps = [ loogle_seccomp ];
      };

      loogle = leanPkgs.buildLeanPackage {
        name = "loogle";
        src = ./.;
        roots = [ "Loogle" ];
        deps = leanPkgs.stdlib ++ [ mathlib4 seccomp ];
        linkFlags = [ "-lseccomp" ];
        overrideBuildModAttrs = self: super: {
          LOOGLE_PATH = mathlib4.modRoot;
        };
      };

      loogle_exe = loogle.executable.overrideAttrs (super: {
        buildInputs = super.buildInputs ++ [ pkgs.pkgsStatic.libseccomp ];
      });
    in
    {
      packages.${system} = {
        inherit loogle_seccomp;
        loogle = loogle_exe;
        mathlib = mathlib4.modRoot;
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
