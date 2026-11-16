import RiffleLowerV2.EmpiricalLower.ManyEdges

set_option warningAsError true

example : RiffleLowerV2.Targets.ManyEdgesTarget :=
  RiffleLowerV2.EmpiricalLower.manyEdges

#check RiffleLowerV2.EmpiricalLower.coldMeanConstant_eq
#check RiffleLowerV2.EmpiricalLower.cold_collision_mean_lower
#check RiffleLowerV2.EmpiricalLower.cold_exponent_slack
#check RiffleLowerV2.EmpiricalLower.cold_mean_dominates
#check RiffleLowerV2.EmpiricalLower.manyEdges
#print axioms RiffleLowerV2.EmpiricalLower.coldMeanConstant_eq
#print axioms RiffleLowerV2.EmpiricalLower.cold_collision_mean_lower
#print axioms RiffleLowerV2.EmpiricalLower.cold_mean_dominates
#print axioms RiffleLowerV2.EmpiricalLower.manyEdges
