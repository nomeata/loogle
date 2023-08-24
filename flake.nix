{
  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.lake2nix.url = "github:Kha/nale?dir=lake2nix";
  inputs.mathlib4.url = "github:leanprover-community/mathlib4/joachim/find";
  inputs.mathlib4.flake = false;
  outputs = { self, nixpkgs, lake2nix, mathlib4 }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};

      mathlib4_flake = lake2nix.lib.lakeRepo2flake {
        name = "mathlib4";
        lean = lake2nix.inputs.lean;
        src = mathlib4;
        depFlakes = [];
      };

      loogle = lake2nix.lib.lakeRepo2flake {
        name = "loogle";
        lean = lake2nix.inputs.lean;
        src = ./.;
        depFlakes = [];
      };

    in
    {
      packages.${system} = {
        mathlib4 = mathlib4_flake.packages.${system}.mathlib4;
        loogle = loogle.packages.${system}.loogle;
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
