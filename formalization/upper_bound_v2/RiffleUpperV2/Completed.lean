import RiffleUpperV2

/-! Complete upper-bound proof exports, each instantiated from its actual implementation. -/
namespace RiffleUpperV2.Completed

theorem firstMoment : Contracts.V1.F := FirstMoment.empiricalFirstMoment
theorem conditionalEdges : Contracts.V1.C := Conditional.remainingCommonEdges
theorem empiricalUpper : Contracts.V1.E := EmpiricalUpper.empiricalUpper
theorem profileUpper : Contracts.V1.P := ProfileUpper.bufferedUpper
theorem criticalUpper : Contracts.V1.T := ProfileUpper.criticalTimeUpper
theorem randomUpper : Contracts.V1.R := ProfileUpper.randomUpper

end RiffleUpperV2.Completed
