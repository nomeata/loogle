{
  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixos-23.11;
  inputs.service.url =  "path:./service"; # edit: use url path syntax

  outputs = { self, nixpkgs, service, ...}@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      my_python = pkgs.python3.withPackages(p: with p; [prometheus-client]);
    in
    {
      nixosConfigurations = service.nixosConfigurations;
      devShells.${system}.default = (pkgs.mkShell.override { stdenv = pkgs.llvmPackages_15.stdenv; }) {
        packages = with pkgs;
          [ elan
            pkgsStatic.libseccomp
            my_python
          ];
      };
    };
}
