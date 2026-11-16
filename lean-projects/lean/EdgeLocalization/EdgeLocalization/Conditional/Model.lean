import EdgeLocalization.Collision.Model

/-! Frozen occupancy-slice definitions O.D01–O.D02.
The forward equivalence is the literal pair of column restrictions. -/

namespace EdgeLocalization

def prefixCounts {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) :
    Fin M → Fin k → ℕ :=
  fun t => n (Fin.castLE hM t)

def suffixCounts {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) :
    Fin (K - M) → Fin k → ℕ :=
  fun t => n ⟨M + t.val, by have ht := t.isLt; omega⟩

def splitMatrix (N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) :
    FixedMatrix N n ≃
      (FixedMatrix N (prefixCounts n hM)) × (FixedMatrix N (suffixCounts n hM)) where
  toFun ω :=
    (fun t => ω (Fin.castLE hM t),
      fun t => ω ⟨M + t.val, by have ht := t.isLt; omega⟩)
  invFun pt j :=
    if hj : j.val < M then
      ⟨(pt.1 ⟨j.val, hj⟩).val, by
        intro a
        simpa only [prefixCounts] using (pt.1 ⟨j.val, hj⟩).property a⟩
    else
      let t : Fin (K - M) := ⟨j.val - M, by have hjK := j.isLt; omega⟩
      ⟨(pt.2 t).val, by
        intro a
        have he : (⟨M + t.val, by have ht := t.isLt; omega⟩ : Fin K) = j := by
          apply Fin.ext
          dsimp only [t]
          omega
        simpa only [suffixCounts, he] using (pt.2 t).property a⟩
  left_inv ω := by
    funext j
    apply Subtype.ext
    funext i
    by_cases hj : j.val < M
    · simp only [dif_pos hj]
      rfl
    · simp only [dif_neg hj]
      have he : (⟨M + (j.val - M), by have hjK := j.isLt; omega⟩ : Fin K) = j := by
        apply Fin.ext
        change M + (j.val - M) = j.val
        omega
      exact congrArg (fun r : Fin K => (ω r).val i) he
  right_inv pt := by
    apply Prod.ext
    · funext t
      apply Subtype.ext
      funext i
      have ht : (Fin.castLE hM t).val < M := t.isLt
      simp only [dif_pos ht]
      rfl
    · funext t
      apply Subtype.ext
      funext i
      have ht : ¬ M + t.val < M := by omega
      simp only [dif_neg ht]
      have he : (⟨M + t.val - M, by have htK := t.isLt; omega⟩ : Fin (K - M)) = t := by
        apply Fin.ext
        change M + t.val - M = t.val
        omega
      exact congrArg (fun r : Fin (K - M) => (pt.2 r).val i) he

end EdgeLocalization
