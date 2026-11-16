import RiffleUpperV2.Shared.Conditioning
import RiffleLowerV2.Thinning.Compat.Conditioning

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RiffleUpperV2
open RiffleLowerV2.Thinning.Compat

/-- The existing finite-law API with exactly the masses of a finite PMF. -/
def toCompatFiniteLaw {Ω : Type*} [Fintype Ω] (P : PMF Ω) : FiniteLaw Ω where
  mass ω := (P ω).toReal
  mass_nonneg _ := ENNReal.toReal_nonneg
  mass_sum := by
    simpa only [RiffleLowerV2.expect, mul_one] using
      RiffleLowerV2.Model.expect_const P 1

@[simp] theorem toCompatFiniteLaw_toPMF {Ω : Type*} [Fintype Ω] (P : PMF Ω) :
    (toCompatFiniteLaw P).toPMF = P := by
  ext ω
  exact ENNReal.ofReal_toReal (P.apply_ne_top ω)

@[simp] theorem toCompatFiniteLaw_expect {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (f : Ω → ℝ) : (toCompatFiniteLaw P).expect f = expect P f := rfl

@[simp] theorem toCompatFiniteLaw_probability {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (E : Ω → Prop) : (toCompatFiniteLaw P).prob E = probability P E := by
  simp only [FiniteLaw.prob, toCompatFiniteLaw, probability,
    RiffleLowerV2.probability, RiffleLowerV2.expect, mul_ite, mul_one, mul_zero]

/-- The old API takes the conditioning event first; the PMF API takes it last. -/
@[simp] theorem toCompatFiniteLaw_conditionalProbability {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (E B : Ω → Prop) :
    (toCompatFiniteLaw P).conditionalProb E B = conditionalProbability P B E := by
  unfold FiniteLaw.conditionalProb conditionalProbability RiffleLowerV2.conditionalProbability
  rw [toCompatFiniteLaw_probability, toCompatFiniteLaw_probability]

@[simp] theorem toCompatFiniteLaw_conditionalExpect {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (E : Ω → Prop) (f : Ω → ℝ) :
    (toCompatFiniteLaw P).conditionalExpect E f = conditionalExpect P f E := by
  unfold FiniteLaw.conditionalExpect conditionalExpect RiffleLowerV2.conditionalExpect
  rw [toCompatFiniteLaw_probability]
  simp only [toCompatFiniteLaw, RiffleLowerV2.expect, mul_ite, mul_zero]

/-- Finite refinement determines a factor map on realized histories. The
arbitrary default is used only outside the image of the fine history. -/
theorem history_refinement_factors {Ω Γ Δ : Type*} (Z : Ω → Γ) (U : Ω → Δ)
    (default : Δ) (h : ∀ ω ω', Z ω = Z ω' → U ω = U ω') :
    ∃ g : Γ → Δ, ∀ ω, U ω = g (Z ω) := by
  let g : Γ → Δ := fun z => if hz : ∃ ω, Z ω = z then U (Classical.choose hz) else default
  refine ⟨g, fun ω => ?_⟩
  have hz : ∃ ω', Z ω' = Z ω := ⟨ω, rfl⟩
  change U ω = if h : ∃ ω', Z ω' = Z ω then U (Classical.choose h) else default
  rw [dif_pos hz]
  exact h ω (Classical.choose hz) (Classical.choose_spec hz).symm

/-- Reuse the proved finite coarse-atom transfer on the actual PMF. The good
event remains inside the endpoint event; no conditioning on that event occurs. -/
theorem shiftedAnticoncentrationTransfer {Ω Γ Δ : Type*}
    [Fintype Ω] [Fintype Γ] [Fintype Δ] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ)
    (hU : ∀ ω, U ω = g (Z ω)) (A : Γ → ℤ) (Y : Ω → ℕ)
    (H : Γ → Prop) (S : Ω → Prop) (hS : ∀ ω, S ω → H (Z ω))
    (b : ℝ) (hb : 0 ≤ b)
    (hpoint : ∀ z, 0 < probability P (fun ω => Z ω = z) → H z → ∀ q : ℕ,
      conditionalProbability P (fun ω => Y ω = q) (fun ω => Z ω = z) ≤ b)
    (u : Δ) (hu : 0 < probability P (fun ω => U ω = u)) (j : ℤ) :
    conditionalProbability P
      (fun ω => A (Z ω) + (Y ω : ℤ) = j ∧ S ω) (fun ω => U ω = u) ≤ b := by
  simpa only [toCompatFiniteLaw_conditionalProbability] using
    FiniteLaw.shifted_anticoncentration_transfer (toCompatFiniteLaw P)
      Z U g hU A Y H S hS b hb
      (by simpa only [toCompatFiniteLaw_probability,
        toCompatFiniteLaw_conditionalProbability] using hpoint)
      u (by simpa only [toCompatFiniteLaw_probability] using hu) j

end RiffleUpperV2
