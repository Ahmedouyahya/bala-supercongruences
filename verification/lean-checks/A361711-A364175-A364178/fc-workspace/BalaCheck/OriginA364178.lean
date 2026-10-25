import BalaCheck.Old.A364178
-- Lists every constant that occurs in the type of the final theorem, with the module that declares it.
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let some ci := env.find? `A364178_from_target | throwError "A364178_from_target not found"
  for c in ci.type.getUsedConstants do
    let mod := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "(current file)"
    IO.println s!"ORIGIN {c} : {mod}"
