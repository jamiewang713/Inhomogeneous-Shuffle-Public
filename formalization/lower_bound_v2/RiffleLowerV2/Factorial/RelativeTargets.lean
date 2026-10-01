import RiffleLowerV2.Factorial.RelativeFromExact
import RiffleLowerV2.Factorial.Exact
import RiffleLowerV2.Factorial.Residual

noncomputable section
namespace RiffleLowerV2.Factorial

/-- The exact canonical matrix moment theorem discharges the numerical input. -/
theorem relativeJointFactorial : Targets.RelativeJointFactorial :=
  relativeJointFactorial_of_exact exactJointFactorial

/-- The exact conditional matrix moment theorem discharges the residual numerical input. -/
theorem residualRelativeFactorial : Targets.ResidualRelativeFactorial :=
  residualRelativeFactorial_of_exact residualJointFactorial

end RiffleLowerV2.Factorial
