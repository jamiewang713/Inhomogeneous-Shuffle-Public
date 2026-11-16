import RiffleTimeProfile.Digits

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Finset

namespace TimeProfile

attribute [local instance] Classical.propDecidable

variable {k K R : ℕ}

/-- D07: the zero-aware sum equals the source's total-weighted entropy. -/
theorem profileH_source_formula (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi C : ℝ) (v M : ℕ)
    (hN : 2 ≤ N) (_hchi : 0 < chi) (_hreg : P.IsRegular chi C)
    (_hlegal : LegalPrefix p x M) :
    profileH N p x P timeClass chi v M =
      ∑ a : Fin R × Fin P.cellCount,
        if 0 < digitTotal N p x P timeClass chi v M a then
          digitTotal N p x P timeClass chi v M a *
            ∑ l : Fin k,
              if 0 < digitCount N p x P timeClass chi v M (a.1, a.2, l) then
                (digitCount N p x P timeClass chi v M (a.1, a.2, l) /
                    digitTotal N p x P timeClass chi v M a) *
                  Real.log (digitTotal N p x P timeClass chi v M a /
                    digitCount N p x P timeClass chi v M (a.1, a.2, l))
              else 0
        else 0 := by
  unfold profileH
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  by_cases ht : 0 < digitTotal N p x P timeClass chi v M a
  · rw [if_pos ht, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs with hc
    · field_simp
    · simp
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro l _
    have hle : digitCount N p x P timeClass chi v M (a.1, a.2, l) ≤
        digitTotal N p x P timeClass chi v M a :=
      Finset.single_le_sum (fun i _ =>
        digitCount_nonneg N p x P timeClass chi v M hN (a.1, a.2, i))
        (Finset.mem_univ l)
    have hnonpos : digitCount N p x P timeClass chi v M (a.1, a.2, l) ≤ 0 :=
      hle.trans (le_of_not_gt ht)
    exact if_neg (not_lt_of_ge hnonpos)

/-- D12: discarding exceptional positions costs at most their count times the uniform psi bound. -/
theorem exceptional_psi_error (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ)
    (hk : 2 ≤ k) (hN : 2 ≤ N) {theta : ℝ} (htheta : theta ∈ Set.Icc (2 : ℝ) 4) :
    ((∑ j ∈ positions K v M, psi (P.rep (P.classify (p j))) theta) / logScale N -
        ∑ a : Fin R × Fin P.cellCount,
          digitTotal N p x P timeClass chi v M a * psi (P.rep a.2) theta) ∈
      Set.Icc 0 (4 * Real.log (k : ℝ) * profileR N p x P chi v M) := by
  have hgroup : (∑ a : Fin R × Fin P.cellCount,
      digitTotal N p x P timeClass chi v M a * psi (P.rep a.2) theta) =
      ∑ a : Fin R × Fin P.cellCount × Fin k,
        digitCount N p x P timeClass chi v M a * psi (P.rep a.2.1) theta := by
    simp only [digitTotal, Fintype.sum_prod_type, Finset.sum_mul]
  have hgood : (∑ a : Fin R × Fin P.cellCount,
      digitTotal N p x P timeClass chi v M a * psi (P.rep a.2) theta) =
      (∑ j ∈ goodPositions p x P chi v M,
        psi (P.rep (P.classify (p j))) theta) / logScale N := by
    rw [hgroup]
    unfold digitCount
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simpa only [Finset.sum_const, nsmul_eq_mul, digitKey] using
      (Finset.sum_fiberwise' (goodPositions p x P chi v M) (digitKey p x P timeClass)
        (fun a => psi (P.rep a.2.1) theta))
  have hsplit : (∑ j ∈ goodPositions p x P chi v M,
      psi (P.rep (P.classify (p j))) theta) +
      (∑ j ∈ exceptionalPositions p x P chi v M,
        psi (P.rep (P.classify (p j))) theta) =
      ∑ j ∈ positions K v M, psi (P.rep (P.classify (p j))) theta :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have herror :
      (∑ j ∈ positions K v M, psi (P.rep (P.classify (p j))) theta) / logScale N -
        (∑ a : Fin R × Fin P.cellCount,
          digitTotal N p x P timeClass chi v M a * psi (P.rep a.2) theta) =
      (∑ j ∈ exceptionalPositions p x P chi v M,
        psi (P.rep (P.classify (p j))) theta) / logScale N := by
    rw [hgood, ← hsplit]
    ring
  rw [herror]
  constructor
  · apply div_nonneg _ (logScale_pos hN).le
    exact Finset.sum_nonneg (fun j _ => (psi_bounds hk (P.rep (P.classify (p j))) htheta).1)
  · calc
      (∑ j ∈ exceptionalPositions p x P chi v M,
          psi (P.rep (P.classify (p j))) theta) / logScale N ≤
        (∑ _j ∈ exceptionalPositions p x P chi v M,
          4 * Real.log (k : ℝ)) / logScale N := by
          apply div_le_div_of_nonneg_right _ (logScale_pos hN).le
          exact Finset.sum_le_sum (fun j _ => (psi_bounds hk (P.rep (P.classify (p j))) htheta).2)
      _ = 4 * Real.log (k : ℝ) * profileR N p x P chi v M := by
        simp only [Finset.sum_const, nsmul_eq_mul, profileR]
        ring

end TimeProfile
