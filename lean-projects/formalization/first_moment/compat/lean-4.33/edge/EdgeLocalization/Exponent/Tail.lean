import EdgeLocalization.Exponent.Model
import EdgeLocalization.Collision.Matrix

/-! Exact finite tail exponent conversion X.06–08 and X.13. -/

noncomputable section

namespace EdgeLocalization

theorem column_square_sum_pos (N : ℕ) {k : ℕ} (n : Fin k → ℕ)
    (hn : ∑ a, n a = N) (hN : 2 ≤ N) :
    0 < ∑ a : Fin k, (singleFactor N n a) ^ 2 := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hex : ∃ a : Fin k, 0 < n a := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have hz : ∑ a, n a = 0 :=
      Finset.sum_eq_zero (fun a _ => Nat.eq_zero_of_le_zero (h a))
    omega
  obtain ⟨a, ha⟩ := hex
  have hp : 0 < singleFactor N n a := by
    exact div_pos (by exact_mod_cast ha) hNpos
  exact lt_of_lt_of_le (sq_pos_of_pos hp)
    (Finset.single_le_sum (fun b _ => sq_nonneg (singleFactor N n b))
      (Finset.mem_univ a))

theorem tailSquareFactor_eq_rpow_tailEdgeExponent (N : ℕ) {K k : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (M : ℕ) (hN : 2 ≤ N) :
    tailSquareFactor N n M = Real.rpow (N : ℝ) (tailEdgeExponent N n M) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNgt).ne'
  have hf (j : Fin K) : 0 < ∑ a : Fin k, (singleFactor N (n j) a) ^ 2 :=
    column_square_sum_pos N (n j) (hn j) hN
  have htail : 0 < tailSquareFactor N n M :=
    Finset.prod_pos (fun j _ => hf j)
  have hlog : Real.log (tailSquareFactor N n M) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin K => M ≤ j.val),
        Real.log (∑ a : Fin k, (singleFactor N (n j) a) ^ 2) := by
    exact Real.log_prod (fun j _ => (hf j).ne')
  have he : tailEdgeExponent N n M =
      Real.log (tailSquareFactor N n M) / Real.log (N : ℝ) := by
    simp only [tailEdgeExponent, columnPsiTwo, Finset.sum_neg_distrib, neg_neg]
    rw [hlog]
  rw [he]
  change tailSquareFactor N n M =
    (N : ℝ) ^ (Real.log (tailSquareFactor N n M) / Real.log (N : ℝ))
  rw [Real.rpow_def_of_pos hNpos]
  have hcancel : Real.log (N : ℝ) *
      (Real.log (tailSquareFactor N n M) / Real.log (N : ℝ)) =
      Real.log (tailSquareFactor N n M) := by
    field_simp [hlogN]
  rw [hcancel, Real.exp_log htail]

theorem tailCollisionFactor_le_rpow_tailEdgeExponent (N : ℕ) {K k : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (M : ℕ) (hN : 2 ≤ N) :
    tailCollisionFactor N n M ≤ Real.rpow (N : ℝ) (tailEdgeExponent N n M) := by
  calc
    _ ≤ tailSquareFactor N n M := tailCollisionFactor_le_tailSquareFactor n hn M hN
    _ = _ := tailSquareFactor_eq_rpow_tailEdgeExponent N n hn M hN

theorem tailEdgeExponent_at_full_length (N : ℕ) {K k : ℕ}
    (n : Fin K → Fin k → ℕ) : tailEdgeExponent N n K = 0 := by
  classical
  have h : (Finset.univ.filter (fun j : Fin K => K ≤ j.val)) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    exact Nat.not_le.mpr j.isLt
  simp only [tailEdgeExponent, h, Finset.sum_empty, neg_zero, zero_div]

end EdgeLocalization
