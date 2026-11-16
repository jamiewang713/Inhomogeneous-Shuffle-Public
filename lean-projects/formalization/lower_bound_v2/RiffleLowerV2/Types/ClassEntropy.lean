import RiffleLowerV2.Types.EntropyBounds
import RiffleLowerV2.Types.Counting

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Types
open TimeProfile
attribute [local instance] Classical.propDecidable

/-- Exact totals make the natural factorial quotient positive. -/
theorem multinomial_quotient_pos {k : ℕ} (n : ℕ) (c : Fin k → ℕ)
    (hc : ∑ l, c l = n) : 0 < n.factorial / ∏ l, (c l).factorial := by
  have ht : ∑ l, c l = Fintype.card (Fin n) := by simpa using hc
  have hcard := prescribedWords_card (J := Fin n) c ht
  simp only [Fintype.card_fin] at hcard
  rw [← hcard]
  exact Finset.card_pos.mpr (prescribedWords_nonempty c ht)

/-- The natural quotient is exact, so its logarithm is the factorial difference. -/
theorem log_multinomial_quotient {k : ℕ} (n : ℕ) (c : Fin k → ℕ)
    (hc : ∑ l, c l = n) :
    Real.log ((n.factorial / ∏ l, (c l).factorial : ℕ) : ℝ) =
      Real.log (n.factorial : ℝ) - ∑ l, Real.log ((c l).factorial : ℝ) := by
  have ht : ∑ l, c l = Fintype.card (Fin n) := by simpa using hc
  have hm := prescribedWords_card_mul (J := Fin n) c ht
  simp only [Fintype.card_fin] at hm
  have hp : 0 < ((prescribedWords (Fin n) (Fin k) c).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (prescribedWords_nonempty c ht)
  have hprod : 0 < ∏ l, ((c l).factorial : ℝ) :=
    Finset.prod_pos (fun l _ => by exact_mod_cast Nat.factorial_pos (c l))
  have hmR : ((prescribedWords (Fin n) (Fin k) c).card : ℝ) *
      (∏ l, ((c l).factorial : ℝ)) = (n.factorial : ℝ) := by
    exact_mod_cast hm
  have hl := congrArg Real.log hmR
  rw [Real.log_mul hp.ne' hprod.ne', Real.log_prod
    (fun l _ => by exact_mod_cast (Nat.factorial_pos (c l)).ne')] at hl
  have hcard := prescribedWords_card (J := Fin n) c ht
  simp only [Fintype.card_fin] at hcard
  rw [← hcard]
  linarith

/-- The exact logarithm of the raw rounded-class cardinality. -/
theorem roundedClass_log_card {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (htotal : ∀ i, ∑ l, D.count i l = cellPositionCount cuts hN P I i) :
    Real.log ((roundedClass cuts hN P I D).card : ℝ) =
      ∑ i, (Real.log ((cellPositionCount cuts hN P I i).factorial : ℝ) -
        ∑ l, Real.log ((D.count i l).factorial : ℝ)) := by
  rw [roundedClass_card cuts hN P I D htotal, Nat.cast_prod]
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl (fun i _ =>
      log_multinomial_quotient _ _ (htotal i))
  · intro i _
    exact_mod_cast (multinomial_quotient_pos _ _ (htotal i)).ne'

/-- Two-sided entropy error for the concrete raw rounded class. -/
theorem roundedClass_entropy_error {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (q : Fin P.cellCount → Fin k → ℝ)
    (htotal : ∀ i, ∑ l, D.count i l = cellPositionCount cuts hN P I i)
    (hq : ∀ i l, 0 ≤ q i l) (hs : ∀ i, ∑ l, q i l = 1)
    (hr : ∀ i l, |(D.count i l : ℝ) -
      (cellPositionCount cuts hN P I i : ℝ)*q i l| ≤ 1) :
    |Real.log ((roundedClass cuts hN P I D).card : ℝ) -
      ∑ i, (cellPositionCount cuts hN P I i : ℝ)*shannonEntropy (q i)| ≤
      (P.cellCount : ℝ)*(2*(k : ℝ)+1)*(Real.log ((I.card : ℝ)+1)+2) := by
  have hsize (i : Fin P.cellCount) : cellPositionCount cuts hN P I i ≤ I.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hbound (i : Fin P.cellCount) :
      |(Real.log ((cellPositionCount cuts hN P I i).factorial : ℝ) -
          ∑ l, Real.log ((D.count i l).factorial : ℝ)) -
        (cellPositionCount cuts hN P I i : ℝ)*shannonEntropy (q i)| ≤
      (2*(k : ℝ)+1)*(Real.log ((I.card : ℝ)+1)+2) := by
    apply (multinomial_log_entropy_error _ (D.count i) (q i)
      (htotal i) (hq i) (hs i) (hr i)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hl : Real.log ((cellPositionCount cuts hN P I i : ℝ)+1) ≤
        Real.log ((I.card : ℝ)+1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hsize i) 1)
    linarith
  rw [roundedClass_log_card cuts hN P I D htotal, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(Real.log ((cellPositionCount cuts hN P I i).factorial : ℝ) -
          ∑ l, Real.log ((D.count i l).factorial : ℝ)) -
        (cellPositionCount cuts hN P I i : ℝ)*shannonEntropy (q i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin P.cellCount,
        (2*(k : ℝ)+1)*(Real.log ((I.card : ℝ)+1)+2) :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end RiffleLowerV2.Types
