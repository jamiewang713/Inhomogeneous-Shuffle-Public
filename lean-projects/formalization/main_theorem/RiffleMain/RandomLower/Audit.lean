import RiffleMain.RandomLower.Forward

/-! Compile this module to inspect the exact random-cut endpoints and their
foundation dependencies, including the common event and full union error. -/

#check RiffleMain.RandomLower.common_event
#check RiffleMain.RandomLower.randomEmpiricalLower
#check RiffleMain.RandomLower.randomEmpiricalLower_tendsto
#print axioms RiffleMain.RandomLower.card_cuts_le
#print axioms RiffleMain.RandomLower.cold_event
#print axioms RiffleMain.RandomLower.common_event
#print axioms RiffleMain.RandomLower.array_scan_error_tendsto
#print axioms RiffleMain.RandomLower.randomEmpiricalLower
#print axioms RiffleMain.RandomLower.randomEmpiricalLower_tendsto
#check RiffleMain.RandomLower.randomForwardLaw
#print axioms RiffleMain.RandomLower.tv_randomInverse_eq_forward
#print axioms RiffleMain.RandomLower.randomEmpiricalLower_forward
#print axioms RiffleMain.RandomLower.randomEmpiricalLower_forward_tendsto
