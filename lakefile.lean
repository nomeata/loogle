import Lake
open Lake DSL

package «loogle» {
  moreLinkArgs :=
   if run_io Option.isSome <$> IO.getEnv "LOOGLE_SECCOMP"
   then #[ "-lseccomp" ]
   else #[]
}

-- require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

meta if run_io Option.isSome <$> IO.getEnv "LOOGLE_SECCOMP" then do
  target loogle_seccomp.o pkg : System.FilePath := do
    let oFile := pkg.buildDir / "loogle_seccomp.o"
    let srcJob ← inputTextFile <| pkg.dir / "loogle_seccomp.c"
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    buildO oFile srcJob flags #[] "cc"

  extern_lib libloogle_seccomp pkg := do
    let name := nameToStaticLib "loogle_seccomp"
    let ffiO ← fetch <| pkg.target ``loogle_seccomp.o
    buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

lean_lib Seccomp where
  roots := #[`Seccomp]
  precompileModules := true

lean_lib Loogle where
  roots := #[`Loogle]
  globs := #[.andSubmodules `Loogle]

lean_lib LoogleMathlibCache where
  roots := #[`LoogleMathlibCache]

lean_lib Tests where
  roots := #[`Tests]

@[default_target]
lean_exe loogle where
  root := `Loogle
  supportInterpreter := true
