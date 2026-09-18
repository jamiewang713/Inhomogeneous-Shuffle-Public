import RiffleTimeProfile.Digits

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Finset

namespace TimeProfile

attribute [local instance] Classical.propDecidable

variable {k K R : ℕ}

/-- D09: the final exceptional digit contributes no representative cost. -/
theorem profileS_append (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ)
    {v M : ℕ} (hvM : v ≤ M) (hMK : M < K) :
    profileS N p x P timeClass chi v (M + 1) -
      profileS N p x P timeClass chi v M =
    if P.IsGoodDigit chi (p ⟨M, hMK⟩) (x ⟨M, hMK⟩) then
      digitCost (prob (P.rep (P.classify (p ⟨M, hMK⟩))) (x ⟨M, hMK⟩)) / logScale N
    else 0 := by
  have hgroup : ∀ m : ℕ, profileS N p x P timeClass chi v m =
      (∑ j ∈ goodPositions p x P chi v m,
        digitCost (prob (P.rep (P.classify (p j))) (x j))) / logScale N := by
    intro m
    simp only [profileS, digitCount, div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simpa only [Finset.sum_const, nsmul_eq_mul, digitKey] using
      (Finset.sum_fiberwise' (goodPositions p x P chi v m) (digitKey p x P timeClass)
        (fun a : Fin R × Fin P.cellCount × Fin k =>
          digitCost (prob (P.rep a.2.1) a.2.2)))
  let jM : Fin K := ⟨M, hMK⟩
  have hpositions : positions K v (M + 1) = insert jM (positions K v M) := by
    ext j
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.ext_iff]
    dsimp [jM]
    omega
  have hnot : jM ∉ goodPositions p x P chi v M := by
    simp [goodPositions, positions, jM]
  rw [hgroup (M + 1), hgroup M]
  by_cases hg : P.IsGoodDigit chi (p jM) (x jM)
  · have hgood : goodPositions p x P chi v (M + 1) =
        insert jM (goodPositions p x P chi v M) := by
      simp only [goodPositions, hpositions, Finset.filter_insert, if_pos hg]
    rw [hgood, Finset.sum_insert hnot, add_div]
    simp only [jM] at hg ⊢
    rw [if_pos hg]
    ring
  · have hgood : goodPositions p x P chi v (M + 1) =
        goodPositions p x P chi v M := by
      simp only [goodPositions, hpositions, Finset.filter_insert, if_neg hg]
    rw [hgood, sub_self]
    exact (if_neg hg).symm

/-- D09: the last good cost is bounded with its explicit dependence on chi. -/
theorem profileS_append_bounds (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ)
    {v M : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hchi : 0 < chi)
    (hchik : chi < 1 / (k : ℝ)) (hvM : v ≤ M) (hMK : M < K) :
    0 ≤ profileS N p x P timeClass chi v (M + 1) -
      profileS N p x P timeClass chi v M ∧
    profileS N p x P timeClass chi v (M + 1) -
      profileS N p x P timeClass chi v M ≤ Real.log (1 / chi) / logScale N := by
  rw [profileS_append N p x P timeClass chi hvM hMK]
  have hL := logScale_pos hN
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hchi_one : chi ≤ 1 := hchik.le.trans (by
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hkreal)
  split_ifs with hg
  · have hrep : 0 < prob (P.rep (P.classify (p ⟨M, hMK⟩))) (x ⟨M, hMK⟩) := by
      dsimp [BorelPartition.IsGoodDigit] at hg
      linarith
    have hchirep : chi ≤ prob (P.rep (P.classify (p ⟨M, hMK⟩))) (x ⟨M, hMK⟩) := by
      dsimp [BorelPartition.IsGoodDigit] at hg
      linarith
    constructor
    · apply div_nonneg _ hL.le
      exact Real.log_nonneg (one_le_one_div hrep (prob_le_one _ _))
    · apply div_le_div_of_nonneg_right _ hL.le
      apply Real.log_le_log (one_div_pos.mpr hrep)
      exact one_div_le_one_div_of_le hchi hchirep
  · exact ⟨le_rfl, div_nonneg (Real.log_nonneg (one_le_one_div hchi hchi_one)) hL.le⟩

/-- D10: the parent condition bounds S without any upper bound on exceptional costs. -/
theorem profile_parent_crossing_bound (N : ℕ) (p : Fin K → Simplex k)
    (x : Fin K → Fin k) (P : BorelPartition k) (timeClass : Fin K → Fin R)
    (chi C b F delta : ℝ) {w v M : ℕ}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hchi : 0 < chi) (hchik : chi < 1 / (k : ℝ))
    (hC : 0 ≤ C) (hreg : P.IsRegular chi C) (hwv : w ≤ v)
    (hM : 0 < M) (hvparent : v ≤ M - 1) (hMK : M ≤ K)
    (hlegal : LegalPrefix p x M) (hdelta : 0 ≤ delta)
    (hparent : delta ≤ cL N p x b w (M - 1) - F) :
    profileS N p x P timeClass chi v M ≤ cL N p x b w v - F +
      C * chi * ((M - 1 - v : ℕ) : ℝ) / logScale N + Real.log (1 / chi) / logScale N := by
  have hparentK : M - 1 < K := by omega
  have hlegalParent : LegalPrefix p x (M - 1) := by
    intro j hj
    apply hlegal j
    omega
  have hcost := (profile_cost_replacement N p x P timeClass chi C b
    hN hchi hC hreg hwv hvparent (by omega) hlegalParent).2
  have hcostUpper := (abs_le.mp hcost).2
  have hQ := profileQ_nonneg N p x P chi C v (M - 1) hN hchi hreg hlegalParent
  have hinc := (profileS_append_bounds N p x P timeClass chi
    hN hk hchi hchik hvparent hparentK).2
  have hpredsucc : M - 1 + 1 = M := by omega
  rw [hpredsucc] at hinc
  linarith

end TimeProfile
