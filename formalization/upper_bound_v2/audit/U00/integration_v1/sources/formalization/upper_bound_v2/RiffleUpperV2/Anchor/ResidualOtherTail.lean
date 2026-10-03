import RiffleUpperV2.Anchor.ResidualOtherLaw

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric RiffleLowerV2.Thinning

/-- The concentration transform gives the one-sided half-mean tail. -/
theorem hypergeomHalfTail (P : RiffleLowerV2.Thinning.Compat.HypergeomParams) :
    probability P.law.toPMF (fun q => (q.val : ℝ) ≤ P.mean/2) ≤
      Real.exp (-RiffleLowerV2.chernoffConstant * P.mean) := by
  exact half_mean_of_transform P.law.toPMF (fun q => q.val) P.mean
    (fun s hs => (transformBound P s hs).1.trans (transformBound P s hs).2)

theorem conditionalProbability_congr_on {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (F : Ω → Prop) {A B : Ω → Prop} (h : ∀ ω, F ω → (A ω ↔ B ω)) :
    conditionalProbability P A F = conditionalProbability P B F := by
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  have he : (fun ω => A ω ∧ F ω) = (fun ω => B ω ∧ F ω) := by
    funext ω
    apply propext
    exact and_congr_left (h ω)
  rw [he]

def residualMean {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A : Finset (Fin n)) (D : Finset (Fin k)) : ℝ :=
  ((n : ℝ)-A.card)*((allowedCount cuts j D : ℝ)/n)

def residualHalfFailure {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A : Sample cuts → Finset (Fin n)) (D : Finset (Fin k)) (ω : Sample cuts) : Prop :=
  ((residualAllowed (A ω) D (ω j)).card : ℝ) ≤ residualMean cuts j (A ω) D / 2

/-- Exact conditional concentration when A is selected by the other columns. -/
theorem residualHalfConditional {k n d : ℕ} (cuts : Cuts k n d)
    (j : Fin d) (A : Sample cuts → Finset (Fin n)) (hA : OtherDetermined j A)
    (D : Finset (Fin k)) (ω₀ : Sample cuts) :
    conditionalProbability (fixedCountPMF cuts) (residualHalfFailure cuts j A D)
      (fun ω => otherColumnHistory j ω = otherColumnHistory j ω₀) ≤
      Real.exp (-RiffleLowerV2.chernoffConstant * residualMean cuts j (A ω₀) D) := by
  trans conditionalProbability (fixedCountPMF cuts)
    (fun ω => ((residualAllowed (A ω) D (ω j)).card : ℝ) ≤ residualMean cuts j (A ω₀) D / 2)
    (fun ω => otherColumnHistory j ω = otherColumnHistory j ω₀)
  · apply le_of_eq
    apply conditionalProbability_congr_on
    intro ω hf
    unfold residualHalfFailure
    rw [hA ω₀ ω ((otherColumnHistory_eq_iff j ω₀ ω).mp hf)]
  · have he := otherResidualConditionalProbability cuts j A hA D ω₀
      (fun q => (q : ℝ) ≤ residualMean cuts j (A ω₀) D / 2)
    have ht := hypergeomHalfTail (otherResidualParams j (A ω₀) D ω₀)
    rw [otherResidualParams_mean] at ht
    exact (le_of_eq he).trans ht

/-- Residual means keep the full-population digit probability and retain at
least the outside-reserve expected count. -/
theorem residualMean_reserve {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (j : Fin d) (R A : Finset (Fin n)) (D : Finset (Fin k)) {g : ℝ}
    (hg : Reserve R g) (hA : A ⊆ R) :
    g * allowedCount cuts j D ≤ residualMean cuts j A D := by
  have ha : (A.card : ℝ) ≤ R.card := by exact_mod_cast Finset.card_le_card hA
  have hr : g * n ≤ (n : ℝ)-A.card := by nlinarith [hg.2.2]
  have hp : 0 ≤ (allowedCount cuts j D : ℝ)/n := by positivity
  calc
    _ = (g*n)*((allowedCount cuts j D : ℝ)/n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hr hp

/-- Actual unconditional lower tail for either residual marked or unmarked
count. The random A may depend on every other column, including suffixes. -/
theorem residualHalfFailure_bound {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (j : Fin d) (R : Finset (Fin n)) (A : Sample cuts → Finset (Fin n))
    (hA : OtherDetermined j A) (hAR : ∀ ω, A ω ⊆ R)
    (D : Finset (Fin k)) {g : ℝ} (hg : Reserve R g) :
    probability (fixedCountPMF cuts) (residualHalfFailure cuts j A D) ≤
      Real.exp (-RiffleLowerV2.chernoffConstant * g * allowedCount cuts j D) := by
  apply probability_le_of_history (fixedCountPMF cuts) (otherColumnHistory j)
  intro ω₀ _
  apply (residualHalfConditional cuts j A hA D ω₀).trans
  apply Real.exp_le_exp.mpr
  have hc := RiffleLowerV2.Thinning.chernoffConstant_pos.le
  have hh := mul_le_mul_of_nonpos_left (residualMean_reserve cuts hn j R (A ω₀) D hg (hAR ω₀))
    (neg_nonpos.mpr hc)
  simpa only [mul_assoc] using hh

end RiffleUpperV2.Anchor
