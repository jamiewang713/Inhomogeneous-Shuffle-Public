import RiffleUpperV2.Shared.Random
import Contracts.v1.Endpoints

/-!
The hypotheses in the current manuscript's Theorem 1.1.  In particular,
`WeaklyInProbability` uses continuous tests of the empirical measure, rather
than requiring any chosen Borel partition to have convergent cell counts.
-/

set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace RiffleMain.Profile
open TimeProfile

/-- Measurability of the family on every Borel subset of the simplex. -/
def MeasurableProfile {k : ℕ} (μ : TimeLaw k) : Prop :=
  ∀ s : Set (Simplex k), MeasurableSet s →
    Measurable (fun t : ℝ => (μ t : Measure (Simplex k)) s)

/-- A positive lower bound on each bounded time interval, modulo null sets. -/
def LocallyNondegenerate {k : ℕ} (μ : TimeLaw k) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ aT : ℝ, 0 < aT ∧
    ∀ᵐ t ∂volume.restrict (Icc 0 T), aT ≤ profileMaxCost μ t

/-- The empirical integral against a continuous test of space and time. -/
def empiricalTest {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (f : Simplex k × ℝ → ℝ) : ℝ :=
  (∑ j : Fin K, f (cuts.profile hN j, columnTime N j)) / logScale N

/-- The limiting test integral for the measure `μ_t(dp) dt`. -/
def profileTest {k : ℕ} (μ : TimeLaw k) (T : ℝ)
    (f : Simplex k × ℝ → ℝ) : ℝ :=
  ∫ t in 0..T, ∫ p, f (p, t) ∂(μ t : Measure (Simplex k))

/-- Weak convergence in probability at one fixed horizon.  Tests need only be
continuous on the compact set used in the manuscript.  Their values outside
that set play no role.  Small decks are omitted by the eventual `2 ≤ N` guard. -/
def WeaklyInProbability {k : ℕ} (μ : TimeLaw k) (T : ℝ)
    (Q : ∀ N, PMF (Cuts k N (horizonDepth N T))) : Prop :=
  ∀ f : Simplex k × ℝ → ℝ, ContinuousOn f (univ ×ˢ Icc 0 T) →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => RiffleUpperV2.probability (Q N) (fun cuts =>
        ∃ hN : 2 ≤ N,
          |empiricalTest cuts (by omega) f - profileTest μ T f| < ε))
        atTop (nhds 1)

/-- The uniform interval conclusion needed by both empirical bounds. -/
def IntervalErrorsInProbability {k : ℕ} (μ : TimeLaw k) (T : ℝ)
    (Q : ∀ N, PMF (Cuts k N (horizonDepth N T))) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => RiffleUpperV2.probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N,
        RiffleLowerV2.Targets.ProfileIntervalErrors T cuts (by omega) μ ε))
      atTop (nhds 1)

/-- Local goodness holds with the same positive constants for every fixed mesh. -/
def LocalGoodInProbability {k : ℕ} (T : ℝ)
    (Q : ∀ N, PMF (Cuts k N (horizonDepth N T))) (g γ : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    Tendsto (fun N => RiffleUpperV2.probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N, TimeProfile.LocalGood cuts (by omega) g γ ρ 0 T))
      atTop (nhds 1)

end RiffleMain.Profile
