import RiffleTimeProfile.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Order.WithBot
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Finset

namespace TimeProfile

variable {k K : ℕ}

/-- Column indices are zero based: this is the paper's interval a < j ≤ b. -/
def positions (K a b : ℕ) : Finset (Fin K) :=
  Finset.univ.filter fun j => a ≤ j.val ∧ j.val < b

def LegalPrefix (p : Fin K → Simplex k) (x : Fin K → Fin k) (M : ℕ) : Prop :=
  ∀ j : Fin K, j.val < M → 0 < prob (p j) (x j)

def prefixWeight (p : Fin K → Simplex k) (x : Fin K → Fin k) (M : ℕ) : ℝ :=
  ∏ j ∈ positions K 0 M, prob (p j) (x j)

/-- Deterministic product mass; its identification with an expectation is separate. -/
def prefixMass (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k) (M : ℕ) : ℝ :=
  (N : ℝ) * prefixWeight p x M

def cL (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (b : ℝ) (w M : ℕ) : ℝ :=
  b - (∑ j ∈ positions K w M, digitCost (prob (p j) (x j))) / logScale N

def cE (N : ℕ) (p : Fin K → Simplex k) (M : ℕ) : ℝ :=
  -(∑ j ∈ positions K M K, psi (p j) 2) / logScale N

def AmbientBlock (p : Fin K → Simplex k) (x : Fin K → Fin k) (w : ℕ) : Prop :=
  w ≤ K ∧ LegalPrefix p x w

def AmbientApproximation (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (w : ℕ) (r b eTime eMass : ℝ) : Prop :=
  |(w : ℝ) / logScale N - r| ≤ eTime ∧
    |Real.log (prefixMass N p x w) / logScale N - b| ≤ eMass

def leftProbability (p : Simplex k) (digit : Fin k) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin k => l < digit), prob p l

def rightProbability (p : Simplex k) (digit : Fin k) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin k => digit < l), prob p l

def sideMass (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (w : ℕ) (side : Simplex k → Fin k → ℝ) (j : Fin K) : ℝ :=
  prefixMass N p x w *
    (∏ h ∈ positions K w j.val, prob (p h) (x h)) * side (p j) (x j)

def sideMaximum (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (w v : ℕ) (side : Simplex k → Fin k → ℝ) : ℝ :=
  ((positions K w v).sup (fun j => Real.toNNReal (sideMass N p x w side j)) : NNReal)

def logExponent (N : ℕ) (z : ℝ) : WithBot ℝ :=
  if z = 0 then ⊥ else (Real.log z / logScale N : ℝ)

def cF (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k) (w v : ℕ) : WithBot ℝ :=
  min (logExponent N (Real.sqrt (sideMaximum N p x w v leftProbability)))
    (logExponent N (Real.sqrt (sideMaximum N p x w v rightProbability)))

def Crossings (p : Fin K → Simplex k) (x : Fin K → Fin k) (w v : ℕ) (chi : ℝ) : Prop :=
  (∃ j ∈ positions K w v, chi ≤ leftProbability (p j) (x j)) ∧
  (∃ j ∈ positions K w v, chi ≤ rightProbability (p j) (x j))

def StableAt (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (b : ℝ) (w M : ℕ) (F delta : ℝ) : Prop :=
  cL N p x b w M - F ≤ delta

def ParentCrossing (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (b : ℝ) (w v M : ℕ) (F delta : ℝ) : Prop :=
  0 < M ∧ v ≤ M - 1 ∧ delta ≤ cL N p x b w (M - 1) - F

/-- D01: legal cylinders have positive mass even when other digits have mass zero. -/
theorem prefixWeight_pos (p : Fin K → Simplex k) (x : Fin K → Fin k)
    {M : ℕ} (hlegal : LegalPrefix p x M) : 0 < prefixWeight p x M := by
  unfold prefixWeight
  apply Finset.prod_pos
  intro j hj
  exact hlegal j (by simpa only [positions, Finset.mem_filter, Finset.mem_univ,
    true_and, Nat.zero_le, true_and] using hj)

theorem prefixWeight_le_one (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (M : ℕ) (hlegal : LegalPrefix p x M) : prefixWeight p x M ≤ 1 := by
  exact Finset.prod_le_one (fun _ _ => prob_nonneg _ _) (fun _ _ => prob_le_one _ _)

theorem prefixWeight_extension_le (p : Fin K → Simplex k) (x : Fin K → Fin k)
    {v M : ℕ} (hvM : v ≤ M) (hlegal : LegalPrefix p x M) :
    prefixWeight p x M ≤ prefixWeight p x v := by
  apply Finset.prod_le_prod_of_subset_of_le_one
  · intro j hj
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  · exact fun _ _ => prob_nonneg _ _
  · exact fun _ _ _ => prob_le_one _ _

theorem prefixMass_pos (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    {M : ℕ} (hN : 0 < N) (hlegal : LegalPrefix p x M) : 0 < prefixMass N p x M := by
  exact mul_pos (by exact_mod_cast hN) (prefixWeight_pos p x hlegal)

/-- D02: no rounding of the ambient length occurs in this split. -/
theorem cL_split (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (b : ℝ) {w v M : ℕ} (hwv : w ≤ v) (hvM : v ≤ M) (hMK : M ≤ K) :
    cL N p x b w M = cL N p x b w v -
      (∑ j ∈ positions K v M, digitCost (prob (p j) (x j))) / logScale N := by
  have hs : positions K w M = positions K w v ∪ positions K v M := by
    ext j
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint (positions K w v) (positions K v M) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    omega
  unfold cL
  rw [hs, Finset.sum_union hd, add_div]
  ring

theorem cL_extension_le (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (b : ℝ) {w v M : ℕ} (hN : 2 ≤ N) (hwv : w ≤ v) (hvM : v ≤ M)
    (hMK : M ≤ K) (hlegal : LegalPrefix p x M) : cL N p x b w M ≤ cL N p x b w v := by
  rw [cL_split N p x b hwv hvM hMK]
  apply sub_le_self
  apply div_nonneg _ (le_of_lt (logScale_pos hN))
  apply Finset.sum_nonneg
  intro j hj
  simp only [digitCost, one_div, Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos (prob_nonneg _ _) (prob_le_one _ _))

theorem cL_exact_mass_exponent (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (b : ℝ) {w M : ℕ} (hN : 2 ≤ N) (hwM : w ≤ M) (hMK : M ≤ K)
    (hlegal : LegalPrefix p x M) :
    Real.log (prefixMass N p x M) / logScale N =
      cL N p x b w M + (Real.log (prefixMass N p x w) / logScale N - b) := by
  have hs : positions K 0 M = positions K 0 w ∪ positions K w M := by
    ext j
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint (positions K 0 w) (positions K w M) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    omega
  have hwp : LegalPrefix p x w := fun j hj => hlegal j (lt_of_lt_of_le hj hwM)
  have hp : ∀ j ∈ positions K w M, prob (p j) (x j) ≠ 0 := by
    intro j hj
    apply ne_of_gt (hlegal j _)
    exact (Finset.mem_filter.mp hj).2.2
  have hm : prefixMass N p x M = prefixMass N p x w *
      ∏ j ∈ positions K w M, prob (p j) (x j) := by
    simp only [prefixMass, prefixWeight, hs, Finset.prod_union hd]
    ring
  have hprod : (∏ j ∈ positions K w M, prob (p j) (x j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hp
  rw [hm, Real.log_mul (ne_of_gt (prefixMass_pos N p x (by omega) hwp)) hprod,
    Real.log_prod hp]
  simp only [cL, digitCost, one_div, Real.log_inv, Finset.sum_neg_distrib]
  ring

theorem cE_nonpos (N : ℕ) (p : Fin K → Simplex k) (M : ℕ)
    (hk : 2 ≤ k) (hN : 2 ≤ N) : cE N p M ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt (logScale_pos hN))
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro j hj
  unfold psi
  apply neg_nonneg.mpr
  apply Real.log_nonpos
  · exact Finset.sum_nonneg fun l _ => Real.rpow_nonneg (prob_nonneg _ _) _
  · calc
      powerSum (p j) 2 ≤ ∑ l : Fin k, prob (p j) l := by
        apply Finset.sum_le_sum
        intro l hl
        rw [Real.rpow_two]
        have h0 := prob_nonneg (p j) l
        have h1 := prob_le_one (p j) l
        nlinarith
      _ = 1 := sum_prob _

theorem cE_terminal (N : ℕ) (p : Fin K → Simplex k) : cE N p K = 0 := by
  have hs : positions K K K = ∅ := by
    ext j
    simp [positions]
  simp [cE, hs]

end TimeProfile
