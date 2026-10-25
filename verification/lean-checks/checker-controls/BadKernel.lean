import Lean
open Lean
-- NEGATIVE CONTROL (scratch, never part of the proofs): a false theorem added WITHOUT kernel checking.
-- `leanchecker` must reject this module.
set_option debug.skipKernelTC true in
run_meta do
  addDecl (.thmDecl { name := `NegControl.bad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
