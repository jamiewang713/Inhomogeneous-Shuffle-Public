import RiffleTimeProfile.Base
import RiffleTimeProfile.Numerical

set_option autoImplicit false

noncomputable section
open Set MeasureTheory

namespace TimeProfile

def localBeta {k : ℕ} (mu : TimeLaw k) (r b s : ℝ) : ℝ :=
  b - integratedMaxCost mu r s

def firstMargin {k : ℕ} (mu : TimeLaw k) (r s u b T : ℝ) : ℝ :=
  sInf ((fun theta : ℝ =>
    (theta + 3) / 2 * localBeta mu r b s - integratedPsi mu theta s u -
      2 * integratedPsi mu 2 u T) '' Icc 3 4)

def secondMargin {k : ℕ} (mu : TimeLaw k) (r s u b T : ℝ) : ℝ :=
  sInf ((fun theta : ℝ =>
    (theta - 1) / 2 * localBeta mu r b s - integratedPsi mu theta s u -
      2 * integratedPsi mu 2 u T) '' Icc 3 4)

def thirdMargin {k : ℕ} (mu : TimeLaw k) (r s b T : ℝ) : ℝ :=
  localBeta mu r b s - integratedPsi mu 2 s T

/-- The literal source margin. No integral approximation theorem is assumed here. -/
def FirstMomentMargin {k : ℕ} (mu : TimeLaw k) (r b T eta : ℝ) : Prop :=
  localBeta mu r b T ≤ -eta ∧
  (∀ s u : ℝ, r ≤ s → s ≤ u → u ≤ T →
    firstMargin mu r s u b T ≤ -eta ∧ secondMargin mu r s u b T ≤ -eta) ∧
  (∀ s : ℝ, r ≤ s → s ≤ T → thirdMargin mu r s b T ≤ -eta)

def WholeDeckMargin {k : ℕ} (mu : TimeLaw k) (T eta : ℝ) : Prop :=
  FirstMomentMargin mu 0 1 T eta

/-- The supplied set must be identified by the separate exploration construction. -/
def RecursiveFirstMomentMargin {k : ℕ} (mu : TimeLaw k)
    (accessible : Set (ℝ × ℝ)) (T eta : ℝ) : Prop :=
  ∀ a ∈ accessible, FirstMomentMargin mu a.1 a.2 T eta

/-- A literal uniform epsilon/N0 formulation, with all members quantified after N0. -/
def UniformlyVanishing {ι : ℕ → Type*} (allowed : ∀ N, Set (ι N))
    (error : ∀ N, ι N → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ x ∈ allowed N,
    |error N x| ≤ epsilon

/-- Chi is chosen before the uniform large-deck threshold. -/
def SubpowerLoss {ι : ℝ → ℕ → Type*} (allowed : ∀ chi N, Set (ι chi N))
    (loss : ∀ chi N, ι chi N → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ chi0 : ℝ, 0 < chi0 ∧
    ∀ chi : ℝ, 0 < chi → chi < chi0 → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ x ∈ allowed chi N, loss chi N x ≤ (N : ℝ) ^ epsilon

instance Cuts.measurableSpace (k N K : ℕ) : MeasurableSpace (Cuts k N K) := ⊤

/-- A law directly on cut arrays; every failure event is measurable in the discrete space.
No independence between the random cut vectors is part of this definition. -/
def RandomizedAlmostLike {k : ℕ} (T rho phi : ℝ)
    (laws : ∀ N, ProbabilityMeasure (Cuts k N (horizonDepth N T)))
    (mu : TimeLaw k) (P : BorelPartition k) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
    ∀ N : ℕ, ∀ hNN : N0 ≤ N,
      (laws N : Measure (Cuts k N (horizonDepth N T)))
        {cuts | ¬ AlmostLike cuts (by omega) mu P T rho phi} ≤
        ENNReal.ofReal epsilon

end TimeProfile
