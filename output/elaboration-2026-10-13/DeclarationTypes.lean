import RiffleMain
import RiffleUpperV2.Completed
import RiffleLowerV2.Completed
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #["RiffleMain", "RiffleUpperV2", "RiffleLowerV2", "Contracts",
    "RiffleShuffle", "RiffleTimeProfile", "FirstMoment", "RiffleProfiles"]
  let owned := env.header.moduleNames.map fun n =>
    roots.any (fun root => n.toString == root || n.toString.startsWith (root ++ "."))
  let rows ← env.constants.foldM (init := (#[] : Array Json)) fun rows name info => do
    let some idx := env.getModuleIdxFor? name | return rows
    unless owned[idx.toNat]! do return rows
    let modName := env.header.moduleNames[idx.toNat]!.toString
    return rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson modName),
      ("levels", toJson (info.levelParams.map Name.toString)),
      ("type_hash", toJson (toString (hash info.type)))]
  let some destination ← IO.getEnv "RIFFLE_TYPE_DUMP"
    | throwError "RIFFLE_TYPE_DUMP is required"
  IO.FS.writeFile destination (Json.arr rows).compress
  logInfo m!"DECLARATION_TYPES_EXPORTED {rows.size}"
