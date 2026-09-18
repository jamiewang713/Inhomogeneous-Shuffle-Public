import Riffle.Model
import RiffleTimeProfile.Base
import RiffleProfiles.WordMass

/-! Frozen T01–T02: the existing model's finite product functional. -/

noncomputable section
open scoped BigOperators

namespace RiffleProfiles

attribute [local instance] Classical.propDecidable

def modelDigitProb (D : Riffle.Model) (j : Fin D.K) (a : Fin D.k) : ℝ :=
  (Riffle.prob D j.val a.val : ℝ)

theorem modelDigitProb_nonneg (D : Riffle.Model) (j : Fin D.K) (a : Fin D.k) :
    0 ≤ modelDigitProb D j a := NNReal.coe_nonneg _

theorem modelDigitProb_sum (D : Riffle.Model) (j : Fin D.K) :
    ∑ a, modelDigitProb D j a = 1 := by
  have hs : ∑ a ∈ Finset.range D.k, (Riffle.prob D j.val a : ℝ) = 1 := by
    exact_mod_cast Riffle.sum_prob D j.val j.isLt
  change (∑ a : Fin D.k, (Riffle.prob D j.val a.val : ℝ)) = 1
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => (Riffle.prob D j.val a : ℝ)) D.k]
  exact hs

def modelColumnProfile (D : Riffle.Model) (j : Fin D.K) : TimeProfile.Simplex D.k :=
  ⟨modelDigitProb D j, modelDigitProb_nonneg D j, modelDigitProb_sum D j⟩

theorem modelColumnProfile_prob (D : Riffle.Model) (j : Fin D.K) (a : Fin D.k) :
    TimeProfile.prob (modelColumnProfile D j) a = modelDigitProb D j a := rfl

theorem model_weight_eq_wordWeight (D : Riffle.Model) (ω : Riffle.FullIndex D) :
    (Riffle.weight D ω : ℝ) = wordWeight (modelDigitProb D) ω := by
  simp only [Riffle.weight, wordWeight, modelDigitProb, NNReal.coe_prod]

theorem model_expectedCount_eq_wordMass (D : Riffle.Model) (E : Set Riffle.Word) :
    (Riffle.expectedCount D E : ℝ) = (D.N : ℝ) *
      ∑ ω : Riffle.FullIndex D,
        if Riffle.fullList ω ∈ E then wordWeight (modelDigitProb D) ω else 0 := by
  classical
  unfold Riffle.expectedCount
  rw [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : Riffle.fullList ω ∈ E
  · simp only [if_pos hω, model_weight_eq_wordWeight]
  · simp only [if_neg hω, NNReal.coe_zero]

theorem model_expectedCount_le_tailWeight (D : Riffle.Model)
    (bad : Fin D.K → Finset (Fin D.k)) (h : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (hbad : ∀ j, (∑ d ∈ bad j, modelDigitProb D j d) ≤ a)
    (E : Set Riffle.Word)
    (hE : ∀ ω : Riffle.FullIndex D, Riffle.fullList ω ∈ E → h ≤ badCount bad ω) :
    (Riffle.expectedCount D E : ℝ) ≤ (D.N : ℝ) * tailWeight D.K h a := by
  classical
  rw [model_expectedCount_eq_wordMass]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D.N)
  calc
    (∑ ω : Riffle.FullIndex D,
        if Riffle.fullList ω ∈ E then wordWeight (modelDigitProb D) ω else 0) ≤
        badWordMass (modelDigitProb D) bad h := by
      rw [badWordMass, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro ω _
      by_cases hω : Riffle.fullList ω ∈ E
      · simp only [if_pos hω, if_pos (hE ω hω), le_refl]
      · simp only [if_neg hω]
        split_ifs
        · exact wordWeight_nonneg _ (modelDigitProb_nonneg D) ω
        · exact le_rfl
    _ ≤ tailWeight D.K h a := by
      simpa only [Fintype.card_fin] using
        badWordMass_le_tailWeight (modelDigitProb D) bad (modelDigitProb_nonneg D)
          (modelDigitProb_sum D) ha hbad h

theorem model_expectedCount_union_le (D : Riffle.Model) (E F : Set Riffle.Word) :
    (Riffle.expectedCount D (E ∪ F) : ℝ) ≤
      (Riffle.expectedCount D E : ℝ) + (Riffle.expectedCount D F : ℝ) := by
  classical
  simp only [model_expectedCount_eq_wordMass, ← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D.N)
  apply Finset.sum_le_sum
  intro ω _
  have hp := wordWeight_nonneg _ (modelDigitProb_nonneg D) ω
  by_cases hE : Riffle.fullList ω ∈ E <;>
    by_cases hF : Riffle.fullList ω ∈ F <;> simp [hE, hF, hp]

end RiffleProfiles
