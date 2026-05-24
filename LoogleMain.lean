/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Loogle
public import Lake.CLI.Error
public import Lake.Util.Cli

/-!
# Entry point of the `loogle` executable

Lives in its own top-level module (outside the `Loogle` library) so the
library can be built with `precompileModules := true` without a build
cycle: the exe links against the lib's shared object, so its entry
point cannot itself be part of the lib.

This is also the right place for the Lake-based CLI argument parsing
— keeping it out of `Loogle.lean` means the precompiled library does
not depend on `libLake_shared.so` at load time.
-/

@[expose] public section

open Lean Loogle

abbrev CliMainM := ExceptT Lake.CliError IO
abbrev CliStateM := StateT LoogleOptions CliMainM
abbrev CliM := Lake.ArgsT CliStateM

def takeArg (arg : String) : CliM String := do
  match (← Lake.takeArg?) with
  | none => throw <| Lake.CliError.missingArg arg
  | some arg => pure arg

def lakeShortOption : (opt : Char) → CliM PUnit
| 'i' => modifyThe LoogleOptions ({· with interactive := true})
| 'j' => modifyThe LoogleOptions ({· with json := true})
| 'h' => modifyThe LoogleOptions ({· with wantsHelp := true})
| opt => throw <| Lake.CliError.unknownShortOption opt

def lakeLongOption : (opt : String) → CliM PUnit
| "--help" => lakeShortOption 'h'
| "--interactive" => lakeShortOption 'i'
| "--json" => lakeShortOption 'j'
| "--path" => do
    let path : System.FilePath ← takeArg "--path"
    modifyThe LoogleOptions fun opts => {opts with searchPath := opts.searchPath ++ [path]}
| "--module" => do modifyThe LoogleOptions ({· with module := ← takeArg "--module"})
| "--index-mode" => do
    let arg ← takeArg "--index-mode"
    let mode ← match arg with
      | "use" => pure IndexMode.useIndex
      | "read" => pure IndexMode.readIndex
      | "write" => pure IndexMode.writeIndex
      | "none" => pure IndexMode.noIndex
      | _ => throw <| Lake.CliError.invalidOptArg "--index-mode" arg
    modifyThe LoogleOptions ({· with indexMode := mode})
| "--index-file" => do
    let path : System.FilePath ← takeArg "--index-file"
    modifyThe LoogleOptions ({· with indexFile := some path})
| "--max-results" => do
    let arg ← takeArg "--max-results"
    let some n := arg.toNat? | throw <| Lake.CliError.invalidOptArg "--max-results" arg
    modifyThe LoogleOptions ({· with maxResults := n})
| opt         => throw <| Lake.CliError.unknownLongOption opt

def lakeOption :=
  Lake.option {
    short := lakeShortOption
    long := lakeLongOption
    longShort := Lake.shortOptionWithArg lakeShortOption
  }

def usage := "
USAGE:
  loogle [OPTIONS] [QUERY]

OPTIONS:
  --help
  --interactive, -i     read querys from stdin
  --json, -j            print result in JSON format
  --module mod          import this module (default: Mathlib)
  --path path           search for .olean files here (default: the build time path)
  --index-mode MODE     how to manage the on-disk search index. One of:
                          use   (default) load if present and up-to-date,
                                otherwise build and write
                          read  load existing index; refuse to start if it
                                is missing or out of date
                          write always (re)build the index and write it
                          none  build in memory and discard on exit
  --index-file PATH     override the default index path. The default lives
                        next to the root module's .olean (with .loogle-index
                        extension); pass this if that location is read-only.
  --max-results n       limit the number of returned hits (default: 200)
" ++
if compileTimeSearchPath.isEmpty then "" else "
Default search path
" ++ String.join (compileTimeSearchPath.map (fun p => s!" * {p}\n"))

unsafe def cliMain : CliM PUnit := do
  match (← Lake.getArgs) with
  | [] => IO.println usage
  | _ => -- normal CLI
    Lake.processOptions lakeOption
    let opts ← getThe LoogleOptions
    let queries ← Lake.takeArgs
    let print := if opts.json then printJson else printPlain
    -- `--write-index` is the only flag that justifies running `work` on its
    -- own (without a query or `--interactive`): the user is asking to rebuild
    -- the cache. `--use-index` is the *default*, so it never counts here.
    let workWithoutQuery := opts.indexMode == .writeIndex
    if opts.wantsHelp ||
      queries.isEmpty && not opts.interactive && not workWithoutQuery
    then IO.println usage
    else work opts  fun index => do
      queries.forM (single index opts.maxResults print)
      if opts.interactive
      then interactive index opts.maxResults print

unsafe def main (args : List String) : IO UInt32 := do
  try
    match (← (cliMain.run args |>.run' {}).run) with
      | .ok _ => return (0 : UInt32)
      | .error e => IO.eprintln e.toString; return 1
  catch e =>
    IO.eprintln e.toString
    return 1
