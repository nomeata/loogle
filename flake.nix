{


  inputs.lean.url = github:nomeata/lean4/for-loogle;
  #inputs.lean.url = github:leanprover/lean4/v4.1.0-rc1;
  # too bad it's too hard to apply a patch to a nix flake input

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.nixpkgs.follows = "lean/nixpkgs";

  inputs.mathlib4.url = "github:leanprover-community/mathlib4/727562596474ad7ecb60549f8b6f77b4510dd917";
  inputs.mathlib4.flake = false;
  inputs.std.url = "github:leanprover/std4/a3b80114adc0948ff493f9acb6ee250f76922d80";
  inputs.std.flake = false;
  inputs.quote4.url = "github:gebner/quote4/d3a1d25f3eba0d93a58d5d3d027ffa78ece07755";
  inputs.quote4.flake = false;
  inputs.aesop.url = "github:JLimperg/aesop/bf5ab42a58e71de7ebad399ce3f90d29aae7fca9";
  inputs.aesop.flake = false;
  inputs.ProofWidgets.url = "github:EdAyers/ProofWidgets4/909febc72b4f64628f8d35cd0554f8a90b6e0749";
  inputs.ProofWidgets.flake = false;

  outputs = { self, nixpkgs, ...}@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      leanPkgs = inputs.lean.packages.${system};

      std = leanPkgs.buildLeanPackage {
        name = "Std";
        src = inputs.std;
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
        deps = [std];
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
        deps = [std];
        overrideBuildModAttrs = addFakeFiles {
          "ProofWidgets.Compat" = [ ".lake/build/js/compat.js" ];
          "ProofWidgets.Component.Basic" = [ ".lake/build/js/interactiveExpr.js" ];
          "ProofWidgets.Component.GoalTypePanel" = [ ".lake/build/js/goalTypePanel.js" ];
          "ProofWidgets.Component.Recharts" = [ ".lake/build/js/recharts.js" ];
          "ProofWidgets.Component.PenroseDiagram" = [ ".lake/build/js/penroseDisplay.js" ];
          "ProofWidgets.Component.Panel.SelectionPanel" = [ ".lake/build/js/presentSelection.js" ];
          "ProofWidgets.Component.Panel.GoalTypePanel" = [ ".lake/build/js/goalTypePanel.js" ];
          "ProofWidgets.Component.MakeEditLink" = [ ".lake/build/js/makeEditLink.js" ];
          "ProofWidgets.Component.OfRpcMethod" = [ ".lake/build/js/ofRpcMethod.js" ];
          "ProofWidgets.Component.HtmlDisplay" =
            [ ".lake/build/js/htmlDisplay.js" ".lake/build/js/htmlDisplayPanel.js"];
          "ProofWidgets.Presentation.Expr" = [ ".lake/build/js/exprPresentation.js" ];
        };
      };

      mathlib4 = leanPkgs.buildLeanPackage {
        name = "Mathlib";
        src = inputs.mathlib4;
        roots = [ { mod = "Mathlib"; glob = "one"; } ];
        leanFlags = [
          "-Dpp.unicode.fun=true"
          "-DautoImplicit=false"
          "-DrelaxedAutoImplicit=false"
        ];
        deps = [std quote4 aesop ProofWidgets];
        overrideBuildModAttrs = addFakeFiles {
          "Mathlib.Tactic.Widget.CommDiag" = [
            "widget/src/penrose/commutative.dsl"
            "widget/src/penrose/commutative.sty"
            "widget/src/penrose/triangle.sub"
            "widget/src/penrose/square.sub"
          ];
        };
      };

      # This creates a self-contained path, so that we don't have to juggle
      # thousands of derivations
      mathlib4_modRoot = pkgs.runCommandCC "Mathlib" {} ''
        mkdir -p $out
        cp -r --reflink=auto --dereference ${mathlib4.modRoot}/* $out/
        ls -l $out
      '';

      loogle_seccomp = pkgs.runCommandCC "loogle_seccomp"
        { buildInputs = [ leanPkgs.leanc pkgs.pkgsStatic.libseccomp ]; } ''
        mkdir -p $out
        cp ${./loogle_seccomp.c} ./loogle_seccomp.c
        leanc -c -o $out/loogle_seccomp.o ./loogle_seccomp.c -fPIC
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
        roots = [ "Loogle" "Tests" ];
        deps = leanPkgs.stdlib ++ [ std seccomp ];
        linkFlags = [ "-lseccomp" ];
      };

      loogle_exe = looglePkg.executable.overrideAttrs (super: {
        buildInputs = super.buildInputs ++ [ pkgs.pkgsStatic.libseccomp ];
      });

      # Loogle also needs the Loogle.Find olean at runtime, for the syntax parser
      # Only copy the Loogle package; the dependencies (std) are included in mathlib4_modRoot.
      loogle_modRoot = pkgs.runCommandCC "Loogle" {} ''
        mkdir -p $out
        cp -r --reflink=auto --dereference ${looglePkg.modRoot}/Loogle $out/
        ls -l $out
      '';


      loogle_index = pkgs.runCommand "loogle.index" { buildInputs = [ loogle_exe ]; } ''
        loogle --path ${mathlib4_modRoot} --path ${loogle_modRoot} --write-index $out
      '';

      loogle = pkgs.runCommand "loogle" { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
        mkdir -p $out/bin
        makeWrapper ${loogle_exe}/bin/loogle $out/bin/loogle --add-flags \
          '--path ${mathlib4_modRoot} --path ${loogle_modRoot} --read-index ${loogle_index}'
      '';

      my_python = pkgs.python3.withPackages(p: with p; [prometheus-client]);

      loogle_server = pkgs.stdenv.mkDerivation {
        name = "loogle_server";
        buildInputs = [ my_python ];
        dontUnpack = true;
        installPhase = ''
          install -Dm755 ${./server.py} $out/bin/loogle_server
          substituteInPlace $out/bin/loogle_server --replace ./build/bin/loogle ${loogle}/bin/loogle
          cp -v ${./blurb.html} $out/blurb.html
          cp -v ${./loogle.png} $out/loogle.png
        '';
      };
    in
    {
      packages.${system} = {
        inherit loogle_seccomp loogle_exe loogle loogle_server loogle_index;
        mathlib = mathlib4_modRoot;
        default = loogle;
      };

      nixosConfigurations.loogle = nixpkgs.lib.nixosSystem {
        inherit system;
        specialArgs = { inherit loogle_server nixpkgs self inputs; };
        modules = [ ./nixos/configuration.nix ];
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
