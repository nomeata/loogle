import Lean

syntax (name := ifEnv)
  "#ifEnv " str " then " ppLine command " else " command :  command

elab_rules : command
  | `(command| #ifEnv $s then $cmd1 else $cmd2) => do
    let s := s.getString
    if (← IO.getEnv s).isSome then do
      Lean.logInfo s!"[INFO] {s} is set"
      Lean.Elab.Command.elabCommandTopLevel cmd1
    else
      Lean.logInfo s!"[INFO] {s} is not set"
      Lean.Elab.Command.elabCommandTopLevel cmd2



#ifEnv "LOOGLE_SECCOMP" then
@[extern "loogle_seccomp"]
def Seccomp.enable : BaseIO Unit := return ()
else
def Seccomp.enable : BaseIO Unit := return ()
