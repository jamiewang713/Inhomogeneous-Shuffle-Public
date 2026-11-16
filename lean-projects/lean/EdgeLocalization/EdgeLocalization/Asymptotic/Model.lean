import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Frozen two-sided ambient-size asymptotic A.D01. -/

namespace EdgeLocalization

def HasSizeExponent (f : ℕ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    Real.rpow (N : ℝ) (b - ε) ≤ f N ∧
    f N ≤ Real.rpow (N : ℝ) (b + ε)

end EdgeLocalization
