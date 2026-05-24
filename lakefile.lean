import Lake
open Lake DSL

package «loogle» {
  moreLinkArgs :=
   if run_io Option.isSome <$> IO.getEnv "LOOGLE_SECCOMP"
   then #[ "-lseccomp" ]
   else #[]
  testDriver := "Tests"
}

meta if run_io Option.isSome <$> IO.getEnv "LOOGLE_SECCOMP" then do
  target loogle_seccomp.o pkg : System.FilePath := do
    let oFile := pkg.buildDir / "loogle_seccomp.o"
    let srcJob ← inputTextFile <| pkg.dir / "loogle_seccomp.c"
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    buildO oFile srcJob flags #[] "cc"

  extern_lib libloogle_seccomp pkg := do
    let name := nameToStaticLib "loogle_seccomp"
    let ffiO ← fetch <| pkg.target ``loogle_seccomp.o
    buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib Seccomp where
  roots := #[`Seccomp]
  precompileModules := true

-- Everything substantive lives in this lib, including the parsers in
-- `Loogle.Parsers`. The lib is precompiled so that
-- `@[builtin_term_parser]` declarations register at import time inside
-- other Lean processes — specifically, the `(⊢ $s)` quotation patterns
-- in `Loogle.Find` rely on those tokens being in the env's table when
-- `Loogle.Find` itself is compiled.
--
-- (Neither `initialize` nor `builtin_initialize` blocks fire during the
-- elaborator's import step — `isInitializerExecutionEnabled` is off
-- there — so the builtin parser only becomes visible via shared-library
-- loading, which is what `precompileModules := true` arranges.)
lean_lib Loogle where
  roots := #[`Loogle]
  globs := #[.andSubmodules `Loogle]
  precompileModules := true

lean_lib Tests where
  roots := #[`Tests]

-- The exe entry point sits in its own top-level module so that this
-- lib doesn't include it. Putting the exe root inside a precompiled
-- lib is a build cycle (the lib's shared object would have to be built
-- before the exe, but the exe is one of the lib's modules).
@[default_target]
lean_exe loogle where
  root := `LoogleMain
  supportInterpreter := true
