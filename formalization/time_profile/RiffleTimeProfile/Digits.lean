import RiffleTimeProfile.Ambient
import RiffleTimeProfile.Analysis
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Finset

namespace TimeProfile

attribute [local instance] Classical.propDecidable

variable {k K R : ℕ}

def goodPositions (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (chi : ℝ) (v M : ℕ) : Finset (Fin K) :=
  (positions K v M).filter fun j => P.IsGoodDigit chi (p j) (x j)

def exceptionalPositions (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (chi : ℝ) (v M : ℕ) : Finset (Fin K) :=
  (positions K v M).filter fun j => ¬ P.IsGoodDigit chi (p j) (x j)

def digitKey (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (j : Fin K) :
    Fin R × Fin P.cellCount × Fin k :=
  (timeClass j, P.classify (p j), x j)

def digitCount (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ)
    (a : Fin R × Fin P.cellCount × Fin k) : ℝ :=
  ((goodPositions p x P chi v M).filter (fun j => digitKey p x P timeClass j = a)).card /
    logScale N

def digitTotal (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ)
    (a : Fin R × Fin P.cellCount) : ℝ :=
  ∑ l : Fin k, digitCount N p x P timeClass chi v M (a.1, a.2, l)

def profileS (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ) : ℝ :=
  ∑ a : Fin R × Fin P.cellCount × Fin k,
    digitCount N p x P timeClass chi v M a * digitCost (prob (P.rep a.2.1) a.2.2)

def profileQ (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (chi : ℝ) (v M : ℕ) : ℝ :=
  (∑ j ∈ exceptionalPositions p x P chi v M, digitCost (prob (p j) (x j))) / logScale N

def profileR (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (chi : ℝ) (v M : ℕ) : ℝ :=
  (exceptionalPositions p x P chi v M).card / logScale N

def profileH (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ) : ℝ :=
  ∑ a : Fin R × Fin P.cellCount, ∑ l : Fin k,
    let c := digitCount N p x P timeClass chi v M (a.1, a.2, l)
    if 0 < c then c * Real.log (digitTotal N p x P timeClass chi v M a / c) else 0

def SameCoarseProfile (N : ℕ) (p : Fin K → Simplex k) (x y : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ) : Prop :=
  digitCount N p x P timeClass chi v M = digitCount N p y P timeClass chi v M ∧
    exceptionalPositions p x P chi v M = exceptionalPositions p y P chi v M

/-- D06: count nonnegativity uses only a positive logarithmic scale. -/
theorem digitCount_nonneg (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ)
    (hN : 2 ≤ N) (a : Fin R × Fin P.cellCount × Fin k) :
    0 ≤ digitCount N p x P timeClass chi v M a := by
  exact div_nonneg (Nat.cast_nonneg _) (logScale_pos hN).le

theorem digitTotal_nonneg (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ)
    (hN : 2 ≤ N) (a : Fin R × Fin P.cellCount) :
    0 ≤ digitTotal N p x P timeClass chi v M a := by
  exact Finset.sum_nonneg fun l _ => digitCount_nonneg N p x P timeClass chi v M hN _

theorem profileR_nonneg (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (chi : ℝ) (v M : ℕ) (hN : 2 ≤ N) :
    0 ≤ profileR N p x P chi v M := by
  exact div_nonneg (Nat.cast_nonneg _) (logScale_pos hN).le

theorem positive_count_support (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ)
    (hN : 2 ≤ N) (a : Fin R × Fin P.cellCount × Fin k)
    (hc : 0 < digitCount N p x P timeClass chi v M a) :
    2 * chi < prob (P.rep a.2.1) a.2.2 := by
  have hcard : 0 < ((goodPositions p x P chi v M).filter
      (fun j => digitKey p x P timeClass j = a)).card := by
    have hr : (0 : ℝ) < ((goodPositions p x P chi v M).filter
        (fun j => digitKey p x P timeClass j = a)).card :=
      (div_pos_iff_of_pos_right (logScale_pos hN)).mp hc
    exact_mod_cast hr
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  obtain ⟨hjgood, hkey⟩ := Finset.mem_filter.mp hj
  have hgood := (Finset.mem_filter.mp hjgood).2
  have hi := congrArg (fun z : Fin R × Fin P.cellCount × Fin k => z.2.1) hkey
  have hl := congrArg (fun z : Fin R × Fin P.cellCount × Fin k => z.2.2) hkey
  dsimp [digitKey] at hi hl
  simpa only [BorelPartition.IsGoodDigit, hi, hl] using hgood

theorem profile_count_partition (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ)
    {v M : ℕ} (hN : 2 ≤ N) (hvM : v ≤ M) (hMK : M ≤ K) :
    (∑ a : Fin R × Fin P.cellCount, digitTotal N p x P timeClass chi v M a) +
      profileR N p x P chi v M = ((M - v : ℕ) : ℝ) / logScale N := by
  have hcard : (positions K v M).card = M - v := by
    calc
      (positions K v M).card = (Finset.Ico v M).card := by
        apply Finset.card_bij (fun j _ => j.val)
        · intro j hj
          simpa only [positions, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_Ico] using hj
        · intro a ha b hb hab
          exact Fin.ext hab
        · intro j hj
          have hm := (Finset.mem_Ico.mp hj).2
          refine ⟨⟨j, lt_of_lt_of_le hm hMK⟩, ?_, rfl⟩
          simpa only [positions, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_Ico] using hj
      _ = M - v := Nat.card_Ico v M
  have hsum : (∑ a : Fin R × Fin P.cellCount × Fin k,
      (((goodPositions p x P chi v M).filter
        (fun j => digitKey p x P timeClass j = a)).card : ℝ)) =
      (goodPositions p x P chi v M).card := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (s := goodPositions p x P chi v M) (t := Finset.univ)
      (f := digitKey p x P timeClass) (fun _ _ => Finset.mem_univ _)).symm
  have hpart : (goodPositions p x P chi v M).card +
      (exceptionalPositions p x P chi v M).card = (positions K v M).card := by
    exact Finset.card_filter_add_card_filter_not _
  simp only [digitTotal, Fintype.sum_prod_type, digitCount, ← Finset.sum_div] at *
  rw [hsum]
  unfold profileR
  rw [← add_div, ← Nat.cast_add, hpart, hcard]

theorem profileS_nonneg (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi C : ℝ) (v M : ℕ)
    (hN : 2 ≤ N) (hchi : 0 < chi) (hreg : P.IsRegular chi C)
    (hlegal : LegalPrefix p x M) : 0 ≤ profileS N p x P timeClass chi v M := by
  apply Finset.sum_nonneg
  intro a ha
  apply mul_nonneg (digitCount_nonneg N p x P timeClass chi v M hN a)
  simp only [digitCost, one_div, Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos (prob_nonneg _ _) (prob_le_one _ _))

theorem profileQ_nonneg (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (chi C : ℝ) (v M : ℕ)
    (hN : 2 ≤ N) (hchi : 0 < chi) (hreg : P.IsRegular chi C)
    (hlegal : LegalPrefix p x M) : 0 ≤ profileQ N p x P chi v M := by
  apply div_nonneg _ (logScale_pos hN).le
  apply Finset.sum_nonneg
  intro j hj
  simp only [digitCost, one_div, Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos (prob_nonneg _ _) (prob_le_one _ _))

theorem profileH_nonneg (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi C : ℝ) (v M : ℕ)
    (hN : 2 ≤ N) (hchi : 0 < chi) (hreg : P.IsRegular chi C)
    (hlegal : LegalPrefix p x M) : 0 ≤ profileH N p x P timeClass chi v M := by
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro l hl
  dsimp
  split_ifs with hc
  · apply mul_nonneg hc.le
    apply Real.log_nonneg
    apply (le_div_iff₀ hc).mpr
    simp only [one_mul]
    exact Finset.single_le_sum (fun l _ => digitCount_nonneg N p x P timeClass chi v M hN (a.1, a.2, l))
      (Finset.mem_univ l)
  · exact le_rfl

/-- D08: exceptional digit costs are retained exactly, without a smallness assumption. -/
theorem profile_cost_replacement (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi C b : ℝ)
    {w v M : ℕ} (hN : 2 ≤ N) (hchi : 0 < chi) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hwv : w ≤ v) (hvM : v ≤ M) (hMK : M ≤ K)
    (hlegal : LegalPrefix p x M) :
    |cL N p x b w M - (cL N p x b w v - profileS N p x P timeClass chi v M -
        profileQ N p x P chi v M)| ≤
      C * chi * (goodPositions p x P chi v M).card / logScale N ∧
    |cL N p x b w M - (cL N p x b w v - profileS N p x P timeClass chi v M -
        profileQ N p x P chi v M)| ≤
      C * chi * ((M - v : ℕ) : ℝ) / logScale N := by
  have hS : profileS N p x P timeClass chi v M =
      (∑ j ∈ goodPositions p x P chi v M,
        digitCost (prob (P.rep (P.classify (p j))) (x j))) / logScale N := by
    unfold profileS digitCount
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simpa only [Finset.sum_const, nsmul_eq_mul, digitKey] using
      (Finset.sum_fiberwise' (goodPositions p x P chi v M) (digitKey p x P timeClass)
        (fun a => digitCost (prob (P.rep a.2.1) a.2.2)))
  have hsplit : (∑ j ∈ goodPositions p x P chi v M, digitCost (prob (p j) (x j))) +
      (∑ j ∈ exceptionalPositions p x P chi v M, digitCost (prob (p j) (x j))) =
      ∑ j ∈ positions K v M, digitCost (prob (p j) (x j)) := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hid : cL N p x b w M -
      (cL N p x b w v - profileS N p x P timeClass chi v M - profileQ N p x P chi v M) =
      -(∑ j ∈ goodPositions p x P chi v M,
        (digitCost (prob (p j) (x j)) - digitCost (prob (P.rep (P.classify (p j))) (x j)))) /
        logScale N := by
    rw [cL_split N p x b hwv hvM hMK, hS, ← hsplit]
    simp only [profileQ, Finset.sum_sub_distrib]
    ring
  have hbound : |cL N p x b w M -
      (cL N p x b w v - profileS N p x P timeClass chi v M - profileQ N p x P chi v M)| ≤
      C * chi * (goodPositions p x P chi v M).card / logScale N := by
    rw [hid, abs_div, abs_neg, abs_of_pos (logScale_pos hN)]
    apply div_le_div_of_nonneg_right _ (logScale_pos hN).le
    calc
      |∑ j ∈ goodPositions p x P chi v M,
          (digitCost (prob (p j) (x j)) - digitCost (prob (P.rep (P.classify (p j))) (x j)))| ≤
        ∑ j ∈ goodPositions p x P chi v M,
          |digitCost (prob (p j) (x j)) - digitCost (prob (P.rep (P.classify (p j))) (x j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ goodPositions p x P chi v M, C * chi := by
        apply Finset.sum_le_sum
        intro j hj
        exact hreg.good_digitCost_error hchi (Finset.mem_filter.mp hj).2
      _ = C * chi * (goodPositions p x P chi v M).card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  refine ⟨hbound, hbound.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (logScale_pos hN).le
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hchi.le)
  have hcard : (positions K v M).card = M - v := by
    calc
      (positions K v M).card = (Finset.Ico v M).card := by
        apply Finset.card_bij (fun j _ => j.val)
        · intro j hj
          simpa only [positions, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_Ico] using hj
        · intro a ha b hb hab
          exact Fin.ext hab
        · intro j hj
          have hm := (Finset.mem_Ico.mp hj).2
          refine ⟨⟨j, lt_of_lt_of_le hm hMK⟩, ?_, rfl⟩
          simpa only [positions, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_Ico] using hj
      _ = M - v := Nat.card_Ico v M
  exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hcard

/-- D11: the entropy comparison is exact before any time-profile approximation. -/
theorem profile_entropy_bound (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ)
    (hN : 2 ≤ N) (hchi : 0 < chi) {theta : ℝ} (htheta : theta ∈ Set.Icc (3 : ℝ) 4) :
    profileH N p x P timeClass chi v M ≤ theta * profileS N p x P timeClass chi v M -
      ∑ a : Fin R × Fin P.cellCount, digitTotal N p x P timeClass chi v M a *
        psi (P.rep a.2) theta := by
  have hg (a : Fin R × Fin P.cellCount) := finite_gibbs (P.rep a.2)
    (fun l => digitCount N p x P timeClass chi v M (a.1, a.2, l))
    (fun l => digitCount_nonneg N p x P timeClass chi v M hN _)
    (by linarith [htheta.1] : 1 ≤ theta)
    (fun l hl => by
      have hp := positive_count_support N p x P timeClass chi v M hN (a.1, a.2, l) hl
      linarith)
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin R × Fin P.cellCount))) => hg a)
  simpa only [profileH, profileS, digitTotal, psi, Fintype.sum_prod_type,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib,
    sub_neg_eq_add] using hsum

theorem same_profile_S_H_R (N : ℕ) (p : Fin K → Simplex k) (x y : Fin K → Fin k)
    (P : BorelPartition k) (timeClass : Fin K → Fin R) (chi : ℝ) (v M : ℕ)
    (h : SameCoarseProfile N p x y P timeClass chi v M) :
    profileS N p x P timeClass chi v M = profileS N p y P timeClass chi v M ∧
    profileH N p x P timeClass chi v M = profileH N p y P timeClass chi v M ∧
    profileR N p x P chi v M = profileR N p y P chi v M := by
  obtain ⟨hc, he⟩ := h
  simp only [profileS, profileH, digitTotal, profileR, hc, he, and_self]

end TimeProfile
