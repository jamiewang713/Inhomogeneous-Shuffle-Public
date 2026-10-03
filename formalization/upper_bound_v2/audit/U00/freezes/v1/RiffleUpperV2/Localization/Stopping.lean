import RiffleUpperV2.Localization.Definitions

noncomputable section
namespace RiffleUpperV2.Localization
open Anchor

theorem firstCut_antichain {k d : ℕ} {v x y : Prefix k d} {Q : Prefix k d → Prop}
    (hx : FirstCut v Q x) (hy : FirstCut v Q y) (hxy : IsPrefix x y) : x = y := by
  by_cases heq : x.1.val = y.1.val
  · exact prefix_eq_of_length hxy heq
  have hlt : x.1.val < y.1.val := lt_of_le_of_ne (prefix_length_le hxy) heq
  rcases hx.2.1 with hqx | hxd
  · exact False.elim (hy.2.2 x hx.1 hxy hlt hqx)
  · have := y.1.isLt
    omega

theorem firstCut_exists {k d : ℕ} {v w : Prefix k d} {Q : Prefix k d → Prop}
    (hw : w.1.val = d) (hvw : IsPrefix v w) :
    ∃ x : Prefix k d, FirstCut v Q x ∧ IsPrefix x w := by
  classical
  have hvlen := prefix_length_le hvw
  have hex : ∃ m : ℕ, ∃ hm : m ≤ w.1.val,
      v.1.val ≤ m ∧ (Q (takePrefix w m hm) ∨ m = d) :=
    ⟨w.1.val, le_rfl, hvlen, Or.inr hw⟩
  let m := Nat.find hex
  obtain ⟨hm, hvm, hstop⟩ := Nat.find_spec hex
  let x := takePrefix w m hm
  have hxw : IsPrefix x w := takePrefix_isPrefix w m hm
  have hvx : IsPrefix v x := by
    apply List.prefix_of_prefix_length_le hvw hxw
    rw [List.Vector.toList_length, List.Vector.toList_length]
    exact hvm
  refine ⟨x, ⟨hvx, hstop, ?_⟩, hxw⟩
  intro u hvu hux hult hqu
  have huw : IsPrefix u w := hux.trans hxw
  have huBound := prefix_length_le huw
  have heq : takePrefix w u.1.val huBound = u := by
    apply prefix_eq_of_length
    · apply List.prefix_of_prefix_length_le (takePrefix_isPrefix _ _ _) huw
      rw [List.Vector.toList_length, List.Vector.toList_length]
      exact le_rfl
    · rfl
  have hmin : m ≤ u.1.val := Nat.find_min' hex
    ⟨huBound, prefix_length_le hvu, Or.inl (heq.symm ▸ hqu)⟩
  change u.1.val < m at hult
  omega

theorem firstCut_existsUnique {k d : ℕ} {v w : Prefix k d} {Q : Prefix k d → Prop}
    (hw : w.1.val = d) (hvw : IsPrefix v w) :
    ∃! x : Prefix k d, FirstCut v Q x ∧ IsPrefix x w := by
  obtain ⟨x, hx, hxw⟩ := firstCut_exists (Q := Q) hw hvw
  refine ⟨x, ⟨hx,hxw⟩, ?_⟩
  intro y hy
  rcases List.prefix_or_prefix_of_prefix hy.2 hxw with h | h
  · exact firstCut_antichain hy.1 hx h
  · exact (firstCut_antichain hx hy.1 h).symm

theorem firstCut_root {k d : ℕ} {v : Prefix k d} {Q : Prefix k d → Prop}
    (hv : Q v ∨ v.1.val = d) : FirstCut v Q v := by
  refine ⟨List.prefix_rfl, hv, ?_⟩
  intro u hvu huv hlt _
  have := prefix_length_le hvu
  omega

theorem firstCut_eq_root {k d : ℕ} {v x : Prefix k d} {Q : Prefix k d → Prop}
    (hv : Q v ∨ v.1.val = d) (hx : FirstCut v Q x) : x = v :=
  (firstCut_antichain (firstCut_root hv) hx hx.1).symm

theorem stableCover {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (v : Prefix k d) (δ : ℝ) {w : Prefix k d}
    (hw : w ∈ FullCylinder cuts R v) :
    ∃! x : Prefix k d, Stable N cuts R v δ x ∧ IsPrefix x w := by
  obtain ⟨x, hx, huniq⟩ := firstCut_existsUnique (Q := Stops N cuts R v δ) hw.2.1 hw.2.2
  refine ⟨x, ⟨⟨legal_prefix cuts hn R hw.1 hx.2,hx.1⟩,hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1.2,hy.2⟩

theorem stable_antichain {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {v : Prefix k d} {δ : ℝ} {x y : Prefix k d}
    (hx : Stable N cuts R v δ x) (hy : Stable N cuts R v δ y) (hxy : IsPrefix x y) :
    x = y := firstCut_antichain hx.2 hy.2 hxy

theorem stable_cylinder_disjoint {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {v : Prefix k d} {δ : ℝ} {x y : Prefix k d}
    (hx : Stable N cuts R v δ x) (hy : Stable N cuts R v δ y) (hne : x ≠ y) :
    Disjoint (FullCylinder cuts R x) (FullCylinder cuts R y) := by
  apply Set.disjoint_left.mpr
  intro w hwx hwy
  rcases List.prefix_or_prefix_of_prefix hwx.2.2 hwy.2.2 with h | h
  · exact hne (stable_antichain hx hy h)
  · exact hne (stable_antichain hy hx h).symm

theorem stable_family_cover {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (v : Prefix k d) (δ : ℝ) :
    (⋃ x : Prefix k d, ⋃ (_ : Stable N cuts R v δ x), FullCylinder cuts R x) =
      FullCylinder cuts R v := by
  ext w
  constructor
  · intro hw
    obtain ⟨x,hx,hwx⟩ := Set.mem_iUnion₂.mp hw
    exact ⟨hwx.1,hwx.2.1,hx.2.1.trans hwx.2.2⟩
  · intro hw
    obtain ⟨x,hx,_⟩ := stableCover N cuts hn R v δ hw
    exact Set.mem_iUnion₂.mpr ⟨x,hx.1,hw.1,hw.2.1,hx.2⟩

theorem proper_parent_not_stopped {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {v : Prefix k d} {δ : ℝ} {x : Prefix k d}
    (hx : ProperStable N cuts R v δ x) :
    IsPrefix v (parent x) ∧ ¬ Stops N cuts R v δ (parent x) := by
  have hvp := prefix_parent hx.1.2.1 hx.2.1
  refine ⟨hvp, hx.1.2.2.2 (parent x) hvp (takePrefix_isPrefix _ _ _) ?_⟩
  change x.1.val - 1 < x.1.val
  have hpos : 0 < x.1.val := lt_of_le_of_lt (Nat.zero_le _) hx.2.1
  omega

theorem proper_join_not_stopped {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {v : Prefix k d} {δ : ℝ} {x : Prefix k d}
    (hx : ProperStable N cuts R v δ x) : ¬ Stops N cuts R v δ v :=
  hx.1.2.2.2 v List.prefix_rfl hx.1.2.1 hx.2.1

theorem stable_cases {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {v : Prefix k d} {δ : ℝ} {x : Prefix k d}
    (hx : Stable N cuts R v δ x) :
    x = v ∨ ProperStable N cuts R v δ x ∨ TerminalFallback N cuts R v δ x := by
  by_cases hstop : Stops N cuts R v δ x
  · by_cases hlen : v.1.val = x.1.val
    · exact Or.inl (prefix_eq_of_length hx.2.1 hlen).symm
    · exact Or.inr (Or.inl ⟨hx, lt_of_le_of_ne (prefix_length_le hx.2.1) hlen, hstop⟩)
  · exact Or.inr (Or.inr ⟨hx,hstop⟩)

theorem fallback_full {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {v : Prefix k d} {δ : ℝ} {x : Prefix k d}
    (hx : TerminalFallback N cuts R v δ x) : x.1.val = d := hx.1.2.2.1.resolve_left hx.2


theorem proper_parent_exponent {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {v : Prefix k d} {δ : ℝ} {x : Prefix k d}
    (hx : ProperStable N cuts R v δ x) :
    boundaryFluctuation N cuts R v + δ ≤ meanExponent N cuts R (parent x) := by
  have h := (proper_parent_not_stopped hx).2
  unfold Stops at h
  linarith

theorem proper_parent_mean {k n d : ℕ} {N : ℕ} (hN : 1 < N)
    {cuts : Cuts k n d} (hn : 0 < n) {R : Finset (Fin n)} {v : Prefix k d}
    {δ : ℝ} {x : Prefix k d} (hx : ProperStable N cuts R v δ x) :
    (N : ℝ) ^ (boundaryFluctuation N cuts R v + δ) ≤ anchoredMean cuts R (parent x) := by
  have hpos : 0 < anchoredMean cuts R (parent x) :=
    legal_prefix cuts hn R hx.1.1 (takePrefix_isPrefix _ _ _)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hexp := proper_parent_exponent hx
  change _ ≤ Real.log (anchoredMean cuts R (parent x)) / Real.log (N : ℝ) at hexp
  have hm := (le_div_iff₀ hlogN).1 hexp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hN)
  rw [Real.rpow_def_of_pos hNpos, ← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hm)

/-- The eventual scale inequality discharges terminal fallback; the model-specific
terminal mean estimate is a separate empirical-cost adapter. -/
theorem stable_no_fallback {k n d : ℕ} {N : ℕ} (hN : 1 < N)
    {cuts : Cuts k n d} (hn : 0 < n) {R : Finset (Fin n)} {v : Prefix k d}
    {δ η q : ℝ}
    (hcomparison : meanExponent N cuts R v - q ≤ 2 * boundaryFluctuation N cuts R v)
    (hterminal : ∀ w : Prefix k d, Legal cuts R w → w.1.val = d → IsPrefix v w →
      meanExponent N cuts R w ≤ -η)
    (hscale : (q-η)/2 < δ) {x : Prefix k d} (hx : Stable N cuts R v δ x) :
    ¬ TerminalFallback N cuts R v δ x := by
  intro hf
  apply hf.2
  exact terminalStops hcomparison
    (meanExponent_antitone N hN cuts hn R hx.1 hx.2.1)
    (hterminal x hx.1 (fallback_full hf) hx.2.1) hscale

end RiffleUpperV2.Localization
