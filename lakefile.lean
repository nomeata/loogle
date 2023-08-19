import Lake
open Lake DSL

package «loogle» {
  -- add any package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"
  @ "9fdeb8945b9fb7ac697fe383e8f48b395fe047b9"

require std from git "https://github.com/leanprover/std4"
  @ "8b864260672b21d964d79ecb2376e01d0eab9f5b"

require aesop from git "https://github.com/JLimperg/aesop"
  @ "d13a9666e6f430b940ef8d092f1219e964b52a09"

require alloy from git "https://github.com/tydeu/lean4-alloy/" @ "master"

extern_lib libseccomp pkg := do
  let name := nameToStaticLib "seccomp"
  let dst := pkg.nativeLibDir / name
  let libdir ← captureProc { cmd := "pkg-config", args := #[ "--variable=libdir", "libseccomp"] }
  logStep s!"Copying {name} from {libdir}"
  proc { cmd := "mkdir", args := #[ "-p", pkg.nativeLibDir.toString] }
  proc { cmd := "cp", args := #[ "-f", s!"{libdir}/{name}", dst.toString] }
  pure $ BuildJob.pure dst

module_data alloy.c.o : BuildJob FilePath
lean_lib Seccomp where
  roots := #[`Seccomp]
  precompileModules := true
  nativeFacets := #[Module.oFacet, `alloy.c.o]

@[default_target]
lean_exe loogle where
  root := `Loogle
  supportInterpreter := true
