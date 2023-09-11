import Lake
open Lake DSL

package «loogle» {
  moreLinkArgs := #[ "-lseccomp" ]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"
  @ "joachim/find"

target loogle_seccomp.o pkg : FilePath := do
  let oFile := pkg.buildDir / "loogle_seccomp.o"
  let srcJob ← inputFile <| pkg.dir / "loogle_seccomp.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO "Seccomp c shim (.o)" oFile srcJob flags "cc"

extern_lib libloogle_seccomp pkg := do
  let name := nameToStaticLib "loogle_seccomp"
  let ffiO ← fetch <| pkg.target ``loogle_seccomp.o
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

target loogle_string.o pkg : FilePath := do
  let oFile := pkg.buildDir / "loogle_string.o"
  let srcJob ← inputFile <| pkg.dir / "loogle_string.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO "String c shim (.o)" oFile srcJob flags "cc"

extern_lib libloogle_string pkg := do
  let name := nameToStaticLib "loogle_string"
  let ffiO ← fetch <| pkg.target ``loogle_string.o
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

lean_lib Loogle where
   roots := #[`Loogle]
   precompileModules := true
  
@[default_target]
lean_exe loogle where
  root := `Loogle
  supportInterpreter := true

@[default_target]
lean_exe testTrie where
  root := `TestTrie
  supportInterpreter := true

