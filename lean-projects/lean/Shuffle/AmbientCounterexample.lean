import Shuffle.HypergeometricBoundary

noncomputable section
open scoped BigOperators

namespace Shuffle

/-- The residual experiment in the manuscript's first-column reveal. -/
def exhaustedParams (L : ℕ) : HypergeomParams where
  population := 2 * L
  marked := L
  draws := 2 * L
  marked_le := by omega
  draws_le := le_rfl

theorem exhausted_expectation (L : ℕ) :
    (exhaustedParams L).law.expect (fun q => (q.val : ℝ)) = (L : ℝ) :=
  (exhaustedParams L).expect_full_draw rfl (fun n => (n : ℝ))

theorem exhausted_variance (L : ℕ) :
    (exhaustedParams L).law.variance (fun q => (q.val : ℝ)) = 0 := by
  rw [HypergeomParams.variance_val]
  simp [HypergeomParams.varianceFormula, exhaustedParams]

theorem exhausted_point_mass (L : ℕ) : (exhaustedParams L).pointMass L = 1 := by
  rw [(exhaustedParams L).pointMass_full_draw rfl]
  simp [exhaustedParams]

theorem exhausted_sample_complement (L : ℕ) (hL : 1 ≤ L) :
    1 - ((exhaustedParams L).draws : ℝ) / (exhaustedParams L).population = 0 := by
  have h : (2 * (L : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    positivity
  simp [exhaustedParams, h]

/-- Positive mean and two positive population categories do not prevent
sampling the entire residual population. This is X1, not an ambient reserve assumption. -/
theorem positive_sides_do_not_prevent_exhaustion (L : ℕ) (hL : 1 ≤ L) :
    0 < (exhaustedParams L).mean ∧
    0 < (exhaustedParams L).marked ∧
    0 < (exhaustedParams L).population - (exhaustedParams L).marked ∧
    (exhaustedParams L).law.variance (fun q => (q.val : ℝ)) = 0 ∧
    (exhaustedParams L).pointMass L = 1 ∧
    1 - ((exhaustedParams L).draws : ℝ) / (exhaustedParams L).population = 0 := by
  have hm : (exhaustedParams L).mean = (L : ℝ) := by
    rw [← (exhaustedParams L).expect_val, exhausted_expectation]
  refine ⟨?_, ?_, ?_, exhausted_variance L, exhausted_point_mass L,
    exhausted_sample_complement L hL⟩
  · rw [hm]
    exact_mod_cast (show 0 < L by omega)
  · change 0 < L
    omega
  · change 0 < 2 * L - L
    omega

theorem fixed_column_middle_endpoints {Ω : Type*} [Fintype Ω]
    (column : Ω → Fin 3) (L M : ℕ)
    (hleft : (Finset.univ.filter (fun ω => column ω = 0)).card = L)
    (hmiddle : (Finset.univ.filter (fun ω => column ω = 1)).card = M) :
    (Finset.univ.filter (fun ω => column ω < 1)).card = L ∧
    (Finset.univ.filter (fun ω => column ω ≤ 1)).card = L + M := by
  classical
  have hlt : (fun ω => column ω < 1) = (fun ω => column ω = 0) := by
    funext ω
    apply propext
    constructor <;> intro h
    · apply Fin.ext
      have : (column ω).val < 1 := h
      simp only [Fin.val_zero]
      omega
    · simp [h]
  have hle : Finset.univ.filter (fun ω => column ω ≤ 1) =
      (Finset.univ.filter (fun ω => column ω = 0)) ∪
        (Finset.univ.filter (fun ω => column ω = 1)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      have hv : (column ω).val ≤ 1 := h
      have hcases : (column ω).val = 0 ∨ (column ω).val = 1 := by omega
      rcases hcases with h0 | h1
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext h1)
    · rintro (h0 | h1)
      · simp [h0]
      · simp [h1]
  have hd : Disjoint (Finset.univ.filter (fun ω => column ω = 0))
      (Finset.univ.filter (fun ω => column ω = 1)) := by
    apply Finset.disjoint_left.mpr
    intro ω h0 h1
    have hz := (Finset.mem_filter.mp h0).2
    have ho := (Finset.mem_filter.mp h1).2
    have : (0 : Fin 3) = 1 := hz.symm.trans ho
    norm_num at this
  have hltset : Finset.univ.filter (fun ω => column ω < 1) =
      Finset.univ.filter (fun ω => column ω = 0) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.of_eq (congrFun hlt ω)
  rw [hltset, hle, Finset.card_union_of_disjoint hd, hleft, hmiddle]
  exact ⟨rfl, rfl⟩

end Shuffle
