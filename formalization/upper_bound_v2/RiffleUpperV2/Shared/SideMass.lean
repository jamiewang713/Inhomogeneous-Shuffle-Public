import RiffleUpperV2.Anchor.Scales

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RiffleUpperV2
open Anchor

/-- Partition a finite product by the first digit which differs from the
selected word. This algebraic identity includes the empty word. -/
theorem finiteProductSidePartition (h : ℕ) (p l r : Fin h → ℝ)
    (hs : ∀ i, p i + l i + r i = 1) :
    (∏ i, p i) +
      (∑ i, (∏ j : Fin i.val, p ⟨j.val, lt_trans j.isLt i.isLt⟩) * l i) +
      (∑ i, (∏ j : Fin i.val, p ⟨j.val, lt_trans j.isLt i.isLt⟩) * r i) = 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hi := ih (fun i => p i.castSucc) (fun i => l i.castSucc)
      (fun i => r i.castSucc) (fun i => hs i.castSucc)
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have he := hs (Fin.last h)
    dsimp only [Fin.val_castSucc, Fin.val_last] at *
    change (∏ i : Fin h, p i.castSucc) * p (Fin.last h) +
      ((∑ i : Fin h, (∏ j : Fin i.val, p ⟨j.val, by omega⟩) * l i.castSucc) +
        (∏ i : Fin h, p i.castSucc) * l (Fin.last h)) +
      ((∑ i : Fin h, (∏ j : Fin i.val, p ⟨j.val, by omega⟩) * r i.castSucc) +
        (∏ i : Fin h, p i.castSucc) * r (Fin.last h)) = 1
    calc
      _ = (∏ i : Fin h, p i.castSucc) *
          (p (Fin.last h) + l (Fin.last h) + r (Fin.last h)) +
          (∑ i : Fin h, (∏ j : Fin i.val, p ⟨j.val, by omega⟩) * l i.castSucc) +
          (∑ i : Fin h, (∏ j : Fin i.val, p ⟨j.val, by omega⟩) * r i.castSucc) := by ring
      _ = 1 := by rw [he, mul_one]; exact hi

theorem digitSideProbabilityPartition {k n d : ℕ} (cuts : Cuts k n d)
    (hn : 0 < n) (j : Fin d) (a : Fin k) :
    digitProbability cuts j a + leftProbability cuts j a +
      rightProbability cuts j a = 1 := by
  have hp (b : Fin k) :
      (if b = a then cuts.count j b else 0) +
      (if b < a then cuts.count j b else 0) +
      (if a < b then cuts.count j b else 0) = cuts.count j b := by
    rcases lt_trichotomy b a with h | h | h <;> simp [h, ne_of_lt, ne_of_gt, not_lt_of_gt]
  have hc : cuts.count j a +
      Hypergeometric.allowedCount cuts j (Finset.univ.filter (· < a)) +
      Hypergeometric.allowedCount cuts j (Finset.univ.filter (a < ·)) = n := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun b _ => hp b)
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Hypergeometric.allowedCount, Finset.sum_filter, cuts.sum_count j] using hh
  unfold digitProbability leftProbability rightProbability
  rw [← add_div, ← add_div, ← Nat.cast_add, ← Nat.cast_add, hc]
  exact div_self (by exact_mod_cast hn.ne')

/-- The actual anchored expected side counts and prefix mean partition |R|. -/
theorem anchoredMassPartition {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (x : Prefix k d) :
    (R.card : ℝ) = anchoredMean cuts R x +
      (∑ i, leftMean cuts R x i) + (∑ i, rightMean cuts R x i) := by
  have h := finiteProductSidePartition x.1.val
    (fun i => digitProbability cuts (prefixColumn x i) (x.2.get i))
    (fun i => leftProbability cuts (prefixColumn x i) (x.2.get i))
    (fun i => rightProbability cuts (prefixColumn x i) (x.2.get i))
    (fun i => digitSideProbabilityPartition cuts hn _ _)
  have hm := congrArg (fun z : ℝ => (R.card : ℝ) * z) h
  symm
  simpa only [anchoredMean, prefixMass, RiffleLowerV2.prefixMass, digitProbability,
    prefixColumn, leftMean, rightMean, sidePrefixMass, mul_add,
    Finset.mul_sum, mul_assoc, mul_one] using hm

/-- Source eq:ub-anchor-side-comparison, second half. Its denominator uses
the original join length, without any lower bound on its expected size. -/
theorem anchoredMass_le_sideMaximum {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) {χ : ℝ} {y z v : Prefix k d}
    (h : GenuineBoundaryPair cuts R χ y z v) :
    (R.card : ℝ) ≤ varianceDenominator χ v * max (leftScale cuts R v) (rightScale cuts R v) := by
  let S := max (leftScale cuts R v) (rightScale cuts R v)
  have hμ : anchoredMean cuts R v ≤ χ⁻¹ * S := by
    have hh := (genuine_sideScale_pos cuts hn R h).2
    have hm : χ * anchoredMean cuts R v ≤ S :=
      hh.trans ((min_le_left _ _).trans (le_max_left _ _))
    have hd : anchoredMean cuts R v ≤ S / χ := (le_div_iff₀ h.chi_pos).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, mul_comm] using hd
  have hl : (∑ i, leftMean cuts R v i) ≤ (v.1.val : ℝ) * S := by
    calc
      _ ≤ ∑ _i : Fin v.1.val, S := Finset.sum_le_sum (fun i _ =>
        (leftMean_le_scale cuts R v i).trans (le_max_left _ _))
      _ = _ := by simp
  have hr : (∑ i, rightMean cuts R v i) ≤ (v.1.val : ℝ) * S := by
    calc
      _ ≤ ∑ _i : Fin v.1.val, S := Finset.sum_le_sum (fun i _ =>
        (rightMean_le_scale cuts R v i).trans (le_max_right _ _))
      _ = _ := by simp
  calc
    _ = anchoredMean cuts R v + (∑ i, leftMean cuts R v i) +
        (∑ i, rightMean cuts R v i) := anchoredMassPartition cuts hn R v
    _ ≤ χ⁻¹ * S + (v.1.val : ℝ) * S + (v.1.val : ℝ) * S := add_le_add (add_le_add hμ hl) hr
    _ = _ := by unfold varianceDenominator S; ring

end RiffleUpperV2
