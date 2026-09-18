import Shuffle
import Lean.Util.FoldConsts

open Lean Elab Command

/- Read-only extraction from the checked environment; it declares no theorem. -/
run_cmd do
  let isProject := fun n : Name =>
    n.toString.startsWith "Shuffle." || n.toString.startsWith "_private.Shuffle."
  let entries ← (← getEnv).constants.foldM (init := (#[] : Array Json)) fun out name info => do
    if !isProject name then
      return out
    let used := info.getUsedConstantsAsSet.toList.toArray
    let localDeps := (used.filter isProject).map (fun n => Json.str n.toString)
    let externalDeps := (used.filter (fun n => !isProject n)).map (fun n => Json.str n.toString)
    return out.push (Json.mkObj [
      ("name", Json.str name.toString),
      ("project_dependencies", Json.arr localDeps),
      ("external_dependencies", Json.arr externalDeps)])
  logInfo (Json.arr entries).compress
