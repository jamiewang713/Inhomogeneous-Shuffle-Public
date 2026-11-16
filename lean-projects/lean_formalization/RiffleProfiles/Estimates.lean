import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite F01–F12 from FROZEN_FINITE_CONTRACT.md.
These are deterministic estimates. No integral or shuffle expectation is defined here.
-/

noncomputable section

open scoped BigOperators

namespace RiffleProfiles

variable {ι κ : Type*}

def cost (p : ℝ) : ℝ := -Real.log p

def normalizedSum (s : Finset ι) (f : ι → ℝ) (L : ℝ) : ℝ :=
  (∑ j ∈ s, f j) / L

def LegalOn (s : Finset ι) (p : ι → ℝ) : Prop :=
  ∀ j ∈ s, 0 < p j ∧ p j ≤ 1

def goodPositions (s : Finset ι) (q : ι → ℝ) (χ : ℝ) : Finset ι :=
  s.filter fun j => 2 * χ < q j

def exceptionalPositions (s : Finset ι) (q : ι → ℝ) (χ : ℝ) : Finset ι :=
  s.filter fun j => ¬2 * χ < q j

structure RegularDigits (s : Finset ι) (p q : ι → ℝ) (χ ε : ℝ) : Prop where
  threshold_pos : 0 < χ
  good_bound : ∀ j ∈ s, 2 * χ < q j →
    χ < p j ∧ |cost (p j) - cost (q j)| ≤ ε
  exceptional_bound : ∀ j ∈ s, q j ≤ 2 * χ → p j ≤ 3 * χ

def goodCost (s : Finset ι) (q : ι → ℝ) (χ L : ℝ) : ℝ :=
  normalizedSum (goodPositions s q χ) (fun j => cost (q j)) L

def exceptionalCost (s : Finset ι) (p q : ι → ℝ) (χ L : ℝ) : ℝ :=
  normalizedSum (exceptionalPositions s q χ) (fun j => cost (p j)) L

def lengthExponent (b : ℝ) (s : Finset ι) (p : ι → ℝ) (L : ℝ) : ℝ :=
  b - normalizedSum s (fun j => cost (p j)) L

theorem cost_eq_log_inverse {p : ℝ} (hp : 0 < p) :
    cost p = Real.log (1 / p) := by
  rw [Real.log_div one_ne_zero (ne_of_gt hp), Real.log_one]
  simp only [cost, zero_sub]

theorem cost_nonnegative {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ cost p := by
  exact neg_nonneg.mpr (Real.log_nonpos hp.le hp1)

theorem cost_antitone {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    cost q ≤ cost p := by
  exact neg_le_neg (Real.log_le_log hp hpq)

theorem good_digit_bounds {s : Finset ι} {p q : ι → ℝ} {χ ε : ℝ}
    (h : RegularDigits s p q χ ε) {j : ι}
    (hj : j ∈ goodPositions s q χ) :
    χ < p j ∧ |cost (p j) - cost (q j)| ≤ ε := by
  exact h.good_bound j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2

theorem exceptional_digit_bound {s : Finset ι} {p q : ι → ℝ} {χ ε : ℝ}
    (h : RegularDigits s p q χ ε) {j : ι}
    (hj : j ∈ exceptionalPositions s q χ) : p j ≤ 3 * χ := by
  exact h.exceptional_bound j (Finset.mem_filter.mp hj).1
    (le_of_not_gt (Finset.mem_filter.mp hj).2)

theorem sum_error_bound (s : Finset ι) (f g : ι → ℝ) :
    |(∑ j ∈ s, f j) - ∑ j ∈ s, g j| ≤ ∑ j ∈ s, |f j - g j| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

theorem normalized_sum_error_bound (s : Finset ι) (f g : ι → ℝ)
    {L ε : ℝ} (hL : 0 < L) (h : ∀ j ∈ s, |f j - g j| ≤ ε) :
    |normalizedSum s f L - normalizedSum s g L| ≤ (s.card : ℝ) * ε / L := by
  unfold normalizedSum
  rw [← sub_div, abs_div, abs_of_pos hL]
  apply div_le_div_of_nonneg_right _ hL.le
  calc
    |(∑ j ∈ s, f j) - ∑ j ∈ s, g j| ≤ ∑ j ∈ s, |f j - g j| :=
      sum_error_bound s f g
    _ ≤ ∑ _j ∈ s, ε := Finset.sum_le_sum h
    _ = (s.card : ℝ) * ε := by simp

theorem good_exceptional_split (s : Finset ι) (f q : ι → ℝ) (χ L : ℝ) :
    normalizedSum s f L =
      normalizedSum (goodPositions s q χ) f L +
      normalizedSum (exceptionalPositions s q χ) f L := by
  unfold normalizedSum goodPositions exceptionalPositions
  rw [← add_div, Finset.sum_filter_add_sum_filter_not]

theorem exceptional_cost_nonnegative {s : Finset ι} {p q : ι → ℝ}
    {χ L : ℝ} (hL : 0 < L) (hp : LegalOn s p) :
    0 ≤ exceptionalCost s p q χ L := by
  apply div_nonneg _ hL.le
  apply Finset.sum_nonneg
  intro j hj
  exact cost_nonnegative (hp j (Finset.mem_filter.mp hj).1).1
    (hp j (Finset.mem_filter.mp hj).1).2

theorem profile_cost_decomposition {s : Finset ι} {p q : ι → ℝ}
    {χ ε L : ℝ} (hL : 0 < L) (h : RegularDigits s p q χ ε) :
    |normalizedSum s (fun j => cost (p j)) L - goodCost s q χ L -
        exceptionalCost s p q χ L| ≤
      ((goodPositions s q χ).card : ℝ) * ε / L := by
  have hrep := normalized_sum_error_bound (goodPositions s q χ)
    (fun j => cost (p j)) (fun j => cost (q j)) hL
    (fun j hj => (good_digit_bounds h hj).2)
  rw [good_exceptional_split s (fun j => cost (p j)) q χ L]
  unfold goodCost exceptionalCost
  convert hrep using 1
  congr 1
  ring

theorem length_exponent_split [DecidableEq ι] (b : ℝ) (s t : Finset ι)
    (p : ι → ℝ) (L : ℝ) (hst : Disjoint s t) :
    lengthExponent b (s ∪ t) p L =
      lengthExponent b s p L - normalizedSum t (fun j => cost (p j)) L := by
  unfold lengthExponent normalizedSum
  rw [Finset.sum_union hst, add_div]
  ring

theorem length_exponent_profile [DecidableEq ι] (b : ℝ) (s t : Finset ι)
    (p q : ι → ℝ) {χ ε L : ℝ} (hL : 0 < L) (hst : Disjoint s t)
    (h : RegularDigits t p q χ ε) :
    |lengthExponent b (s ∪ t) p L - lengthExponent b s p L +
        goodCost t q χ L + exceptionalCost t p q χ L| ≤
      ((goodPositions t q χ).card : ℝ) * ε / L := by
  rw [length_exponent_split b s t p L hst]
  have heq : lengthExponent b s p L - normalizedSum t (fun j => cost (p j)) L -
      lengthExponent b s p L + goodCost t q χ L + exceptionalCost t p q χ L =
      -(normalizedSum t (fun j => cost (p j)) L - goodCost t q χ L -
        exceptionalCost t p q χ L) := by ring
  rw [heq, abs_neg]
  exact profile_cost_decomposition hL h

theorem cell_regrouping [Fintype κ] [DecidableEq κ] (s : Finset ι)
    (cell : ι → κ) (v : κ → ℝ) (L : ℝ) :
    normalizedSum s (fun j => v (cell j)) L =
      ∑ i, (((s.filter fun j => cell j = i).card : ℝ) / L) * v i := by
  have h : (∑ j ∈ s, v (cell j)) =
      ∑ i, ((s.filter fun j => cell j = i).card : ℝ) * v i := by
    simpa using (Finset.sum_fiberwise' s cell v).symm
  unfold normalizedSum
  rw [h, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem cell_replacement [Fintype κ] [DecidableEq κ] (s : Finset ι)
    (cell : ι → κ) (f : ι → ℝ) (v m δ : κ → ℝ) {L ε : ℝ}
    (hL : 0 < L) (hrep : ∀ j ∈ s, |f j - v (cell j)| ≤ ε)
    (hcount : ∀ i, |((s.filter fun j => cell j = i).card : ℝ) / L - m i| ≤ δ i) :
    |normalizedSum s f L - ∑ i, m i * v i| ≤
      (s.card : ℝ) * ε / L + ∑ i, |v i| * δ i := by
  have hfirst := normalized_sum_error_bound s f (fun j => v (cell j)) hL hrep
  have hsecond : |normalizedSum s (fun j => v (cell j)) L - ∑ i, m i * v i| ≤
      ∑ i, |v i| * δ i := by
    rw [cell_regrouping s cell v L]
    apply (sum_error_bound Finset.univ _ _).trans
    apply Finset.sum_le_sum
    intro i _hi
    rw [← sub_mul, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hcount i) (abs_nonneg (v i))
  calc
    |normalizedSum s f L - ∑ i, m i * v i| ≤
        |normalizedSum s f L - normalizedSum s (fun j => v (cell j)) L| +
        |normalizedSum s (fun j => v (cell j)) L - ∑ i, m i * v i| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hfirst hsecond

theorem interval_blocking (blocks : Finset ι) (empirical target : ι → ℝ)
    {empiricalEnd targetEnd L ρ T φ B : ℝ}
    (hL : 0 < L) (he0 : 0 ≤ empiricalEnd) (ht0 : 0 ≤ targetEnd)
    (he : empiricalEnd ≤ 2 * ρ + 2 / L) (ht : targetEnd ≤ 2 * ρ)
    (hblocks : (∑ i ∈ blocks, |empirical i - target i|) ≤ T * φ + B / L) :
    |((∑ i ∈ blocks, empirical i) + empiricalEnd) -
        ((∑ i ∈ blocks, target i) + targetEnd)| ≤
      4 * ρ + T * φ + (B + 2) / L := by
  have hmain := sum_error_bound blocks empirical target
  have hend : |empiricalEnd - targetEnd| ≤ empiricalEnd + targetEnd := by
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have htriangle := abs_add
    ((∑ i ∈ blocks, empirical i) - ∑ i ∈ blocks, target i)
    (empiricalEnd - targetEnd)
  have hrewrite : ((∑ i ∈ blocks, empirical i) + empiricalEnd) -
      ((∑ i ∈ blocks, target i) + targetEnd) =
      ((∑ i ∈ blocks, empirical i) - ∑ i ∈ blocks, target i) +
        (empiricalEnd - targetEnd) := by ring
  rw [hrewrite]
  have hdiv : (B + 2) / L = B / L + 2 / L := add_div B 2 L
  have hL0 : L ≠ 0 := ne_of_gt hL
  linarith

theorem tail_cell_replacement [Fintype κ] [DecidableEq κ] (s : Finset ι)
    (cell : ι → κ) (f : ι → ℝ) (v m δ : κ → ℝ) {L ε : ℝ}
    (hL : 0 < L) (hrep : ∀ j ∈ s, |f j - v (cell j)| ≤ ε)
    (hcount : ∀ i, |((s.filter fun j => cell j = i).card : ℝ) / L - m i| ≤ δ i) :
    |(-normalizedSum s f L) - (-(∑ i, m i * v i))| ≤
      (s.card : ℝ) * ε / L + ∑ i, |v i| * δ i := by
  rw [neg_sub_neg, abs_sub_comm]
  exact cell_replacement s cell f v m δ hL hrep hcount

theorem maximal_pile_domination (s : Finset ι) (p maximal : ι → ℝ)
    (b : ℝ) {L : ℝ} (hL : 0 < L)
    (hp : ∀ j ∈ s, 0 < p j) (hmax : ∀ j ∈ s, p j ≤ maximal j) :
    lengthExponent b s p L ≤ b - normalizedSum s (fun j => cost (maximal j)) L := by
  unfold lengthExponent normalizedSum
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ hL.le
  exact Finset.sum_le_sum fun j hj => cost_antitone (hp j hj) (hmax j hj)

theorem maximal_pile_target {actual target bound b e : ℝ}
    (hmax : bound ≤ b - actual) (herr : |actual - target| ≤ e) :
    bound ≤ b - target + e := by
  have he := (abs_le.mp herr).1
  linarith

theorem side_mass_ge_continuation (s : Finset ι) (p : ι → ℝ)
    {χ earlier side : ℝ} (hχ : 0 < χ) (he : 0 ≤ earlier)
    (hp0 : ∀ j ∈ s, 0 ≤ p j) (hp1 : ∀ j ∈ s, p j ≤ 1)
    (hside : χ * earlier ≤ side) :
    χ * (earlier * ∏ j ∈ s, p j) ≤ side := by
  have hprod : (∏ j ∈ s, p j) ≤ 1 := Finset.prod_le_one hp0 hp1
  exact (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right he hprod) hχ.le).trans hside

theorem fluctuation_log_comparison {L χ M U V : ℝ}
    (hL : 0 < L) (hχ : 0 < χ) (hM : 0 < M) (hU : 0 < U) (hV : 0 < V)
    (hleft : χ * M ≤ U) (hright : χ * M ≤ V) :
    (Real.log M + Real.log χ) / (2 * L) ≤
      min (Real.log U / (2 * L)) (Real.log V / (2 * L)) := by
  have hleftLog := (Real.log_le_log_iff (mul_pos hχ hM) hU).mpr hleft
  have hrightLog := (Real.log_le_log_iff (mul_pos hχ hM) hV).mpr hright
  rw [Real.log_mul (ne_of_gt hχ) (ne_of_gt hM)] at hleftLog hrightLog
  apply le_min
  · exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem parent_crossing_good_cost {Q parent base Sparent Sx F δ e d : ℝ}
    (hQ : 0 ≤ Q) (herr : |parent - base + Sparent + Q| ≤ e)
    (hparent : δ ≤ parent - F) (hδ : 0 ≤ δ) (hstep : Sx ≤ Sparent + d) :
    Sx ≤ base - F + e + d := by
  have hupper := (abs_le.mp herr).2
  linarith

end RiffleProfiles
