import RiffleTimeProfile.Base

/- Provenance: the quadratureError definition from RiffleTimeProfile.AnalyticParameters.
Only this numerical definition is needed by the fresh GridQuadrature port. -/
noncomputable section
namespace RiffleLowerV2.ProfileTransfer.Compat
open TimeProfile
def quadratureError (N : ℕ) (T rho phi : ℝ) (m : ℕ) (M omega : ℝ) : ℝ :=
  2 * omega * T + M * m * phi * T + 2 * M * rho +
    (omega + M + 2 * M * m) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N
end RiffleLowerV2.ProfileTransfer.Compat
