import EdgeLocalization.Overlap.FiniteLaw
import EdgeLocalization.Collision.Estimates

/-! Frozen same-position edge-overlap identities and bounds S.04–06. -/

namespace EdgeLocalization

theorem edgeDensity_eq_expected_shared_internal_edges {Ω : Type*} [Fintype Ω]
    (w : FiniteLaw Ω) (N : ℕ) (R : Ω → ℕ → List ℕ) (xList : List ℕ) :
    edgeDensity w N R xList =
      (w.prod w).expectation (fun z =>
        ((internalEdges N (R z.1) xList ∩ internalEdges N (R z.2) xList).card : ℝ)) := by
  simpa only [edgeDensity, edgeProbability, pow_two] using
    (w.expected_card_intersection w (Finset.range (N - 1))
      (fun ω => internalEdges N (R ω) xList) (fun ω => internalEdges N (R ω) xList)
      (fun ω => internalEdges_subset_range N (R ω) xList)
      (fun ω => internalEdges_subset_range N (R ω) xList)).symm

theorem matrix_expected_shared_internal_edges_le_mean_tail_fourth {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    ((matrixLaw n hn).prod (matrixLaw n hn)).expectation (fun z =>
      ((internalEdges N (sortedRows n z.1) (prefixWord x) ∩
        internalEdges N (sortedRows n z.2) (prefixWord x)).card : ℝ)) ≤
      (prefixMean N n hM x) ^ 4 * (tailCollisionFactor N n M) ^ 2 / 4 := by
  calc
    _ = edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) :=
      (edgeDensity_eq_expected_shared_internal_edges
        (matrixLaw n hn) N (sortedRows n) (prefixWord x)).symm
    _ ≤ _ := matrix_internal_density_le_mean_tail_fourth n hn hM x

theorem matrix_expected_shared_internal_edges_le_prefixMean {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    ((matrixLaw n hn).prod (matrixLaw n hn)).expectation (fun z =>
      ((internalEdges N (sortedRows n z.1) (prefixWord x) ∩
        internalEdges N (sortedRows n z.2) (prefixWord x)).card : ℝ)) ≤
      prefixMean N n hM x := by
  calc
    _ = edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) :=
      (edgeDensity_eq_expected_shared_internal_edges
        (matrixLaw n hn) N (sortedRows n) (prefixWord x)).symm
    _ ≤ _ := matrix_internal_density_le_prefixMean n hn hM x

end EdgeLocalization
