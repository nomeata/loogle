{
  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.lean.url = "github:leanprover/lean4";
  outputs = { self, lean, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      leanPkgs = lean.packages.${system};
      lakePkg = leanPkgs.buildLeanPackage {
        name = "Loogle";
        src = ./.;
      };
    in
    {
      # doesn't work yet, need to package dependencies and think about
      # (or ditch) alloy
      packages.${system} = lakePkg;
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
