import RiffleUpperV2.Anchor.Definitions
import RiffleUpperV2.Localization.Prefixes

noncomputable section
namespace RiffleUpperV2.Anchor

/-- An empty local prefix is the exposed anchor, and cannot be a post-anchor crossing. -/
theorem no_leftCrossing_at_anchor {k n d : ℕ} (cuts : Cuts k n d) (χ : ℝ)
    (x : Prefix k d) (hx : x.1.val = 0) : ¬ LeftCrossing cuts χ x := by
  rintro ⟨h,_⟩
  omega

theorem no_rightCrossing_at_anchor {k n d : ℕ} (cuts : Cuts k n d) (χ : ℝ)
    (x : Prefix k d) (hx : x.1.val = 0) : ¬ RightCrossing cuts χ x := by
  rintro ⟨h,_⟩
  omega

theorem genuine_join_positive_depth {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) {χ : ℝ} {y z v : Prefix k d}
    (h : GenuineBoundaryPair cuts R χ y z v) : 0 < v.1.val := by
  obtain ⟨hy,_⟩ := h.left_crossing
  have hle := RiffleUpperV2.Localization.prefix_length_le h.left_prefix
  omega

/-- The fixed-pile endpoint counterexample is retained literally in the model. -/
theorem anchor_lowerEndpoint_deterministic {k n d : ℕ} {cuts : Cuts k n d}
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (hx : x.1.val = 0)
    (ω : Sample cuts) : lowerEndpoint c₀ R x ω = c₀ := by
  have hnil : x.2.toList = [] := List.length_eq_zero_iff.mp (by simp [hx])
  simp [lowerEndpoint, hx, hnil]

theorem anchor_upperEndpoint_deterministic {k n d : ℕ} {cuts : Cuts k n d}
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (hx : x.1.val = 0)
    (ω : Sample cuts) : upperEndpoint c₀ R x ω = c₀ + R.card := by
  have hnil : x.2.toList = [] := List.length_eq_zero_iff.mp (by simp [hx])
  rw [upperEndpoint, anchor_lowerEndpoint_deterministic c₀ R x hx ω]
  simp [prefixRows, hx, hnil]

/-- There is no smoothing boundary pair when no future column remains. -/
theorem no_genuine_when_depth_zero {k n : ℕ} (cuts : Cuts k n 0)
    (R : Finset (Fin n)) (χ : ℝ) (y z v : Prefix k 0) :
    ¬ GenuineBoundaryPair cuts R χ y z v := by
  intro h
  have hp := genuine_join_positive_depth cuts R h
  have hv := v.1.isLt
  omega

end RiffleUpperV2.Anchor
