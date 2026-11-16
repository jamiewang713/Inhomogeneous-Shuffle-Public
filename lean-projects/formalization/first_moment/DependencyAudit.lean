import FirstMoment
import FirstMomentModel
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let nsPrefix := "InhomogeneousShuffle.FirstMoment."
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if nsPrefix.isPrefixOf name.toString then
      let dependencies := info.getUsedConstantsAsSet.toArray.map (fun n => n.toString)
      rows := rows.push (Json.mkObj [
        ("name", toJson name.toString),
        ("directConstants", toJson dependencies)])
  logInfo (Json.compress (Json.mkObj [
    ("scope", toJson "Elaborated types and values in the first-moment namespace"),
    ("declarations", toJson rows)]))
