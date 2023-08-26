{
  inputs.lean.url = github:leanprover/lean4/39c9e2a4d13dcb5ad76566fe5dda0c80b95171b2;

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.nixpkgs.follows = "lean/nixpkgs";

  inputs.mathlib4.url = "github:leanprover-community/mathlib4/joachim/find";
  inputs.mathlib4.flake = false;
  inputs.std4.url = "github:leanprover/std4/8b864260672b21d964d79ecb2376e01d0eab9f5b";
  inputs.std4.flake = false;
  inputs.quote4.url = "github:gebner/quote4/81cc13c524a68d0072561dbac276cd61b65872a6";
  inputs.quote4.flake = false;
  inputs.aesop.url = "github:JLimperg/aesop/d13a9666e6f430b940ef8d092f1219e964b52a09";
  inputs.aesop.flake = false;
  inputs.ProofWidgets.url = "github:EdAyers/ProofWidgets4/a0c2cd0ac3245a0dade4f925bcfa97e06dd84229";
  inputs.ProofWidgets.flake = false;

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

      # addFakeFile can plug into buildLeanPackage’s overrideBuildModAttrs
      # it takes a lean module name and a filename, and makes that file available
      # (as an empty file) in the build tree, e.g. for include_str.
      addFakeFiles = m: self: super:
        if m ? ${super.name}
        then let
          paths = m.${super.name};
        in {
          src = pkgs.runCommandCC "${super.name}-patched" {
            inherit (super) leanPath src relpath;
          } (''
            dir=$(dirname $relpath)
            mkdir -p $out/$dir
            if [ -d $src ]; then cp -r $src/. $out/$dir/; else cp $src $out/$leanPath; fi
          '' + pkgs.lib.concatMapStringsSep "\n" (p : ''
            install -D -m 644 ${pkgs.emptyFile} $out/${p}
          '') paths);
        }
        else {};

      ProofWidgets = leanPkgs.buildLeanPackage {
        name = "ProofWidgets";
        src = inputs.ProofWidgets;
        roots = [ "ProofWidgets" ];
        deps = [std4];
        overrideBuildModAttrs = addFakeFiles {
          "ProofWidgets.Compat" = [ "build/js/compat.js" ];
          "ProofWidgets.Component.Basic" = [ "build/js/interactiveExpr.js" ];
          "ProofWidgets.Component.GoalTypePanel" = [ "build/js/goalTypePanel.js" ];
          "ProofWidgets.Component.Recharts" = [ "build/js/recharts.js" ];
          "ProofWidgets.Component.PenroseDiagram" = [ "build/js/penroseDisplay.js" ];
          "ProofWidgets.Component.SelectionPanel" = [ "build/js/presentSelection.js" ];
          "ProofWidgets.Component.HtmlDisplay" =
            [ "build/js/htmlDisplay.js" "build/js/htmlDisplayPanel.js"];
          "ProofWidgets.Presentation.Expr" = [ "build/js/exprPresentation.js" ];
        };
      };

      mathlib4 = leanPkgs.buildLeanPackage {
        name = "Mathlib";
        # src = inputs.mathlib4;
        # I did not figure out how to build ProofWidgets4 with buildLeanPackage, so I am patching
        # it out. Unfortunately, the following also puts all sources files into a single
        # store path, instead of having each source file being its own source (inputs.mathlib4 is a
        # lazy tree, not derivation!). This mean even more recomputation. Oh well.
        src = pkgs.applyPatches {
          name = "mathlib4-patched";
          src = inputs.mathlib4;
          postPatch = ''
            sed -i '/Widget/d' ./Mathlib.lean ./Mathlib/Tactic.lean
          '';
        };
        roots = [ { mod = "Mathlib"; glob = "one"; } ];
        leanFlags = [
          "-Dpp.unicode.fun=true"
          "-DautoImplicit=false"
          "-DrelaxedAutoImplicit=false"
        ];
        deps = [std4 quote4 aesop ProofWidgets];
        overrideBuildModAttrs = addFakeFiles {
          "Mathlib.Tactic.Widget.CommDiag" = [
            "widget/src/penrose/commutative.dsl"
            "widget/src/penrose/commutative.sty"
            "widget/src/penrose/triangle.sub"
            "widget/src/penrose/square.sub"
          ];
        };
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

      looglePkg = leanPkgs.buildLeanPackage {
        name = "loogle";
        src = ./.;
        roots = [ "Loogle" ];
        deps = leanPkgs.stdlib ++ [ mathlib4 seccomp ];
        linkFlags = [ "-lseccomp" ];
      };

      loogle_exe = looglePkg.executable.overrideAttrs (super: {
        buildInputs = super.buildInputs ++ [ pkgs.pkgsStatic.libseccomp ];
      });

      loogle_index = pkgs.runCommand "loogle.index" { buildInputs = [ loogle_exe ]; } ''
        loogle --path ${mathlib4.modRoot} --write-index $out
      '';

      loogle = pkgs.runCommand "loogle" { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
        mkdir -p $out/bin
        makeWrapper ${loogle_exe}/bin/loogle $out/bin/loogle --add-flags \
          '--path ${mathlib4.modRoot} --read-index ${loogle_index}'
      '';

      loogle_server = pkgs.stdenv.mkDerivation {
        name = "loogle_server";
        buildInputs = [ pkgs.python3 ];
        dontUnpack = true;
        installPhase = ''
          install -Dm755 ${./server.py} $out/bin/loogle_server
          substituteInPlace $out/bin/loogle_server --replace ./build/bin/loogle ${loogle}/bin/loogle
          substituteInPlace $out/bin/loogle_server --replace blurb.html ${./blurb.html}
        '';
      };
    in
    {
      packages.${system} = {
        inherit loogle_seccomp loogle_exe loogle loogle_server;
        mathlib = mathlib4.modRoot;
        default = loogle;
      };

      nixosConfigurations.loogle = nixpkgs.lib.nixosSystem {
        inherit system;
        specialArgs = { inherit loogle_server nixpkgs; };
        modules = [ ./nixos/configuration.nix ];
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
