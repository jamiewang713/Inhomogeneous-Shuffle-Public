import RiffleLowerV2.Factorial.Main
open RiffleLowerV2
#check (Factorial.exactJointFactorial : Targets.ExactJointFactorial)
#check (Factorial.relativeJointFactorial : Targets.RelativeJointFactorial)
#check (Factorial.residualJointFactorial : Targets.ResidualJointFactorial)
#check (Factorial.residualRelativeFactorial : Targets.ResidualRelativeFactorial)
#check (Factorial.residualMeanComparison : Targets.ResidualMeanComparison)
#check (Factorial.bonferroniSandwich : Targets.BonferroniSandwich)
#check (Factorial.bonferroniProduct : Targets.BonferroniProduct)
#check (Factorial.centralComparison : Targets.CentralComparison)
#check (Factorial.centralComparisonOne : Targets.CentralComparisonOne)
#check (Factorial.rareSandwich : Targets.RareSandwich)
#print axioms Factorial.exactJointFactorial
#print axioms Factorial.relativeJointFactorial
#print axioms Factorial.residualJointFactorial
#print axioms Factorial.residualRelativeFactorial
#print axioms Factorial.residualMeanComparison
#print axioms Factorial.bonferroniSandwich
#print axioms Factorial.bonferroniProduct
#print axioms Factorial.centralComparison
#print axioms Factorial.centralComparisonOne
#print axioms Factorial.rareSandwich
#print Targets.ExactJointFactorial
#print Targets.RelativeJointFactorial
#print Targets.ResidualJointFactorial
#print Targets.ResidualRelativeFactorial
#print Targets.ResidualMeanComparison
#print Targets.BonferroniSandwich
#print Targets.BonferroniProduct
#print Targets.CentralComparison
#print Targets.CentralComparisonOne
#print Targets.RareSandwich
#check Factorial.conditional_wordCount_eq_residualWordMean
#print axioms Factorial.conditional_wordCount_eq_residualWordMean
