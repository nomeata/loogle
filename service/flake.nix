{
  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixos-23.11;

  outputs = { self, nixpkgs, ...}@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      my_python = pkgs.python3.withPackages(p: with p; [prometheus-client]);
    in
    {
      packages.${system} = {
        loogle-updater =
          let deps = [
            pkgs.gitMinimal
            pkgs.elan
            pkgs.coreutils
            pkgs.curl
            pkgs.pkg-config
            pkgs.llvmPackages_15.clang
            pkgs.gnugrep
            pkgs.gnutar
            pkgs.gzip
          ]; in
          pkgs.runCommand "loogle-updater"
            { nativeBuildInputs = [ pkgs.makeWrapper ]; }
            ''
              install -m755 ${./build.sh} -D $out/bin/loogle-updater
              patchShebangs $out/bin/loogle-updater
              wrapProgram $out/bin/loogle-updater \
                --set PATH ${pkgs.lib.makeBinPath deps } \
                --prefix NIX_CFLAGS_COMPILE_x86_64_unknown_linux_gnu " " "-I${pkgs.pkgsStatic.libseccomp.dev}/include" \
                --prefix NIX_LDFLAGS_x86_64_unknown_linux_gnu " " "-L${pkgs.pkgsStatic.libseccomp.lib}/lib" \
            '';
      };

      nixosConfigurations.loogle = nixpkgs.lib.nixosSystem {
        inherit system;
        specialArgs = { inherit nixpkgs self; };
        modules = [ ./configuration.nix ];
      };

      devShells.${system}.default = (pkgs.mkShell.override { stdenv = pkgs.llvmPackages_15.stdenv; }) {
        packages = with pkgs;
          [ elan
            pkgsStatic.libseccomp
            pkgconfig
            my_python
          ];
      };
    };
}
