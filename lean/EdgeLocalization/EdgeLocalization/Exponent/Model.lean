import EdgeLocalization.Collision.Model
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Frozen exponent definitions X.D01–X.D05. -/

noncomputable section

namespace EdgeLocalization

def legalPrefix {K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hM : M ≤ K) (x : Fin M → Fin k) : Prop :=
  ∀ t : Fin M, 0 < n (Fin.castLE hM t) (x t)

def ambientSizeExponent (N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hM : M ≤ K) (A : ℕ) (b : ℝ) (x : Fin M → Fin k) : ℝ :=
  b - (∑ t ∈ Finset.univ.filter (fun t : Fin M => A ≤ t.val),
    Real.log ((N : ℝ) / (n (Fin.castLE hM t) (x t) : ℝ))) / Real.log (N : ℝ)

def ambientMeanError (N : ℕ) {K k A : ℕ} (n : Fin K → Fin k → ℕ)
    (hA : A ≤ K) (w : Fin A → Fin k) (b : ℝ) : ℝ :=
  Real.log (prefixMean N n hA w) / Real.log (N : ℝ) - b

def columnPsiTwo (N : ℕ) {k : ℕ} (n : Fin k → ℕ) : ℝ :=
  -Real.log (∑ a : Fin k, (singleFactor N n a) ^ 2)

def tailEdgeExponent (N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ)
    (M : ℕ) : ℝ :=
  -(∑ j ∈ Finset.univ.filter (fun j : Fin K => M ≤ j.val),
    columnPsiTwo N (n j)) / Real.log (N : ℝ)

end EdgeLocalization
