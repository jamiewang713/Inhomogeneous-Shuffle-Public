import RiffleUpperV2.Exploration.Histories
import RiffleLowerV2.Thinning.PMFTools

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open RiffleLowerV2.Thinning

private theorem expect_by_fibers {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : PMF Ω) (Z : Ω → Γ) (f : Γ → ℝ) :
    RiffleLowerV2.expect P (fun ω => f (Z ω)) =
      ∑ z, RiffleLowerV2.probability P (fun ω => Z ω = z) * f z := by
  change (∑ ω, (P ω).toReal * f (Z ω)) =
    ∑ z, (∑ ω, (P ω).toReal * (if Z ω = z then 1 else 0)) * f z
  simp only [Finset.sum_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

private theorem weighted_conditionalProbability {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (A B : Ω → Prop) :
    RiffleLowerV2.probability P B * RiffleLowerV2.conditionalProbability P A B =
      RiffleLowerV2.probability P (fun ω => A ω ∧ B ω) := by
  unfold RiffleLowerV2.conditionalProbability
  by_cases hb : RiffleLowerV2.probability P B = 0
  · have ha : RiffleLowerV2.probability P (fun ω => A ω ∧ B ω) = 0 :=
      le_antisymm (by simpa [hb] using (probability_mono P (A := fun ω => A ω ∧ B ω)
        (B := B) (fun _ h => h.2))) (probability_nonneg _ _)
    simp only [hb, ha, zero_div, mul_zero]
  · exact mul_div_cancel₀ _ hb

/-- Tower identity for the actual finite conditional-RiffleLowerV2.probability quotient, including null fibers. -/
theorem conditionalProbability_tower {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : PMF Ω) (Z : Ω → Γ) (A : Ω → Prop) :
    RiffleLowerV2.expect P (fun ω => RiffleLowerV2.conditionalProbability P A (fun v => Z v = Z ω)) =
      RiffleLowerV2.probability P A := by
  rw [expect_by_fibers P Z (fun z => RiffleLowerV2.conditionalProbability P A (fun v => Z v = z))]
  simp_rw [weighted_conditionalProbability]
  simp only [RiffleLowerV2.probability, RiffleLowerV2.expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : A ω <;> simp [ha, mul_ite]

/-- Conditional Markov, with the exceptional RiffleLowerV2.probability supplied by the concrete event. -/
theorem conditionalProbability_markov {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : PMF Ω) (Z : Ω → Γ) (A : Ω → Prop) {ε : ℝ} (hε : 0 < ε) :
    RiffleLowerV2.probability P (fun ω => ε <
      RiffleLowerV2.conditionalProbability P A (fun v => Z v = Z ω)) ≤
        RiffleLowerV2.probability P A / ε := by
  have hn (ω : Ω) : 0 ≤ RiffleLowerV2.conditionalProbability P A (fun v => Z v = Z ω) :=
    div_nonneg (probability_nonneg _ _) (probability_nonneg _ _)
  calc
    _ ≤ RiffleLowerV2.probability P (fun ω => ε ≤
        RiffleLowerV2.conditionalProbability P A (fun v => Z v = Z ω)) :=
      probability_mono P (fun _ h => h.le)
    _ ≤ _ := by
      have hm := markov P hn hε
      rw [conditionalProbability_tower P Z A] at hm
      exact hm

/-- The source threshold is sqrt(r_bad), not a RiffleLowerV2.probability-conditioned history. -/
theorem historyGoodProbability {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ r : ℝ) (hr : 0 < r)
    (hH : RiffleLowerV2.probability (fixedCountPMF cuts) (fun ω => ¬ concentrationEvent cuts D g ξ ω) ≤ r)
    (p : Fin k) (d : Direction) (i : ℕ) :
    RiffleLowerV2.probability (fixedCountPMF cuts)
      (fun ω => ¬ historyGood cuts D g ξ (Real.sqrt r) p d i ω) ≤ Real.sqrt r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hm := conditionalProbability_markov (fixedCountPMF cuts)
    (naturalHistory cuts p d i) (fun ω => ¬ concentrationEvent cuts D g ξ ω) hs
  change RiffleLowerV2.probability (fixedCountPMF cuts)
    (fun ω => ¬ RiffleLowerV2.conditionalProbability (fixedCountPMF cuts)
      (fun v => ¬ concentrationEvent cuts D g ξ v)
      (fun v => naturalHistory cuts p d i v = naturalHistory cuts p d i ω) ≤ Real.sqrt r) ≤ _
  simp only [not_le]
  calc
    _ ≤ _ := hm
    _ ≤ r / Real.sqrt r := div_le_div_of_nonneg_right hH hs.le
    _ = Real.sqrt r := by rw [div_eq_iff hs.ne', Real.mul_self_sqrt hr.le]

end RiffleUpperV2.Exploration
