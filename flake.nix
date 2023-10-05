{
  inputs.lean.url = github:nomeata/lean4/for-loogle;
  #inputs.lean.url = github:leanprover/lean4/v4.1.0-rc1;

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.nixpkgs.follows = "lean/nixpkgs";

  inputs.mathlib4.url = "github:leanprover-community/mathlib4/joachim/find";
  inputs.mathlib4.flake = false;
  inputs.std4.url = "github:leanprover/std4/67855403d60daf181775fa1ec63b04e70bcc3921";
  inputs.std4.flake = false;
  inputs.quote4.url = "github:gebner/quote4/e75daed95ad1c92af4e577fea95e234d7a8401c1";
  inputs.quote4.flake = false;
  inputs.aesop.url = "github:JLimperg/aesop/1a0cded2be292b5496e659b730d2accc742de098";
  inputs.aesop.flake = false;
  inputs.ProofWidgets.url = "github:EdAyers/ProofWidgets4/65bba7286e2395f3163fd0277110578f19b8170f";
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
          "ProofWidgets.Component.Panel.SelectionPanel" = [ "build/js/presentSelection.js" ];
          "ProofWidgets.Component.Panel.GoalTypePanel" = [ "build/js/goalTypePanel.js" ];
          "ProofWidgets.Component.MakeEditLink" = [ "build/js/makeEditLink.js" ];
          "ProofWidgets.Component.OfRpcMethod" = [ "build/js/ofRpcMethod.js" ];
          "ProofWidgets.Component.HtmlDisplay" =
            [ "build/js/htmlDisplay.js" "build/js/htmlDisplayPanel.js"];
          "ProofWidgets.Presentation.Expr" = [ "build/js/exprPresentation.js" ];
        };
      };

      build_mathlib4 = pruned: leanPkgs.buildLeanPackage {
        name = "Mathlib";
        # src = inputs.mathlib4;
        # To build less, if pruned == true, then only the modules actally
        # needed by loogle the executable are built
        src = if pruned
          then pkgs.applyPatches {
            name = "mathlib4-${if pruned then "pruned" else "patched"}";
            src = inputs.mathlib4;
            postPatch = ''
              echo "import Mathlib.Tactic.Find"  > Mathlib.lean
            '';
          }
          else inputs.mathlib4;
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

      mathlib4_pruned = build_mathlib4 true;
      mathlib4 = build_mathlib4 false;

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
        roots = [ "Loogle" ];
        deps = leanPkgs.stdlib ++ [ mathlib4_pruned seccomp ];
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
          cp -v ${./blurb.html} ${./loogle.png} $out/
        '';
      };
    in
    {
      packages.${system} = {
        inherit loogle_seccomp loogle_exe loogle loogle_server loogle_index;
        mathlib = mathlib4.modRoot;
        mathlib_pruned = mathlib4_pruned.modRoot;
        default = loogle;
      };

      nixosConfigurations.loogle = nixpkgs.lib.nixosSystem {
        inherit system;
        specialArgs = { inherit loogle_server nixpkgs self; };
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
