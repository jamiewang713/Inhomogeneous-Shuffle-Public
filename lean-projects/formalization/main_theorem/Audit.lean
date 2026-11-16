import RiffleMain
import Lean.Util.CollectAxioms

#check RiffleMain.main
#check RiffleMain.cutoff
#check RiffleMain.infinite_critical
#check RiffleMain.main_random_sequence
#check RiffleMain.cutoff_random_sequence
#check RiffleMain.infinite_critical_random_sequence
#check RiffleMain.theorem_1_1
#print axioms RiffleMain.main
#print axioms RiffleMain.cutoff
#print axioms RiffleMain.infinite_critical
#print axioms RiffleMain.main_random_sequence
#print axioms RiffleMain.cutoff_random_sequence
#print axioms RiffleMain.infinite_critical_random_sequence
#print axioms RiffleMain.theorem_1_1

open Lean Elab Command in
run_cmd do
  for decl in [``RiffleMain.main, ``RiffleMain.cutoff,
      ``RiffleMain.infinite_critical, ``RiffleMain.main_random_sequence,
      ``RiffleMain.cutoff_random_sequence, ``RiffleMain.infinite_critical_random_sequence,
      ``RiffleMain.theorem_1_1] do
    let axs ← Lean.collectAxioms decl
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "Unaccepted dependency {a} in {decl}"
  logInfo "MAIN_THEOREM_TRUST_OK"
