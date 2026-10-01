import RiffleLowerV2.Thinning.PMFTools

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Localization
attribute [local instance] Classical.propDecidable

theorem probability_add_complement {Ω : Type*} [Fintype Ω] (P : PMF Ω) (A : Ω → Prop) :
    probability P A + probability P (fun omega => ¬A omega) = 1 := by
  have htotal : (∑ omega, (P omega).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun omega _ => P.apply_ne_top omega)]
    have h := P.tsum_coe
    rw [tsum_fintype] at h
    rw [h]
    simp
  unfold probability expect
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ omega, (P omega).toReal := by
      apply Finset.sum_congr rfl
      intro omega _
      by_cases h : A omega <;> simp [h]
    _ = 1 := htotal

theorem probability_ge_one_sub_failure {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (A B : Ω → Prop) {e : ℝ} (h : ∀ omega, A omega → B omega)
    (hfail : probability P (fun omega => ¬A omega) ≤ e) :
    1-e ≤ probability P B := by
  have hc := probability_add_complement P A
  have hm := Thinning.probability_mono P h
  linarith

end RiffleLowerV2.Localization
