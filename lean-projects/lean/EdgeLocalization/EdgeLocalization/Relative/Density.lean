import EdgeLocalization.Relative.Deck
import EdgeLocalization.Overlap.FiniteLaw
import EdgeLocalization.Collision.Estimates

/-! Frozen relative-density estimates R.08–R.13. -/

noncomputable section

namespace EdgeLocalization

theorem relative_density_le_sq_expected_absolute_edges {Ω : Type*} [Fintype Ω]
    (w : FiniteLaw Ω) (N : ℕ) (R : Ω → ℕ → List ℕ) (xList : List ℕ)
    (shift : Ω → ℕ) :
    relativeEdgeDensity w N R xList shift ≤
      (w.expectation (fun ω => (edgeCount N (R ω) xList : ℝ))) ^ 2 := by
  let H : Ω → Finset ℕ := fun ω => relativeInternalEdges N (R ω) xList (shift ω)
  have hH (ω : Ω) : H ω ⊆ Finset.range (N - 1) :=
    relativeInternalEdges_subset_range N (R ω) xList (shift ω)
  have hs : (∑ i ∈ Finset.range (N - 1), w.probability (fun ω => i ∈ H ω)) =
      w.expectation (fun ω => ((H ω).card : ℝ)) :=
    w.sum_probabilities_eq_expected_card (Finset.range (N - 1)) H hH
  have hm : w.expectation (fun ω => ((H ω).card : ℝ)) ≤
      w.expectation (fun ω => (edgeCount N (R ω) xList : ℝ)) := by
    apply w.expectation_mono
    intro ω
    exact_mod_cast relativeInternalEdges_card_le N (R ω) xList (shift ω)
  have he : 0 ≤ w.expectation (fun ω => ((H ω).card : ℝ)) :=
    w.expectation_nonneg _ (fun _ => Nat.cast_nonneg _)
  calc
    relativeEdgeDensity w N R xList shift ≤
        (∑ i ∈ Finset.range (N - 1), w.probability (fun ω => i ∈ H ω)) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg
        (fun i _ => w.probability_nonneg (fun ω => i ∈ H ω))
    _ = (w.expectation (fun ω => ((H ω).card : ℝ))) ^ 2 :=
      congrArg (fun z : ℝ => z ^ 2) hs
    _ ≤ _ := by
      simpa only [pow_two] using mul_le_mul hm hm he (le_trans he hm)

theorem relative_density_le_expected_occupancy {Ω : Type*} [Fintype Ω]
    (w : FiniteLaw Ω) (N : ℕ) (R : Ω → ℕ → List ℕ) (xList : List ℕ)
    (shift : Ω → ℕ) :
    relativeEdgeDensity w N R xList shift ≤
      w.expectation (fun ω => (occupancyCount N (R ω) xList : ℝ)) := by
  calc
    relativeEdgeDensity w N R xList shift ≤
        w.expectation (fun ω =>
          ((relativeInternalEdges N (R ω) xList (shift ω)).card : ℝ)) :=
      w.sum_sq_probabilities_le_expected_card (Finset.range (N - 1))
        (fun ω => relativeInternalEdges N (R ω) xList (shift ω))
        (fun ω => relativeInternalEdges_subset_range N (R ω) xList (shift ω))
    _ ≤ _ := by
      apply w.expectation_mono
      intro ω
      exact_mod_cast le_trans
        (relativeInternalEdges_card_le N (R ω) xList (shift ω))
        (internalEdges_card_le_occupancy N (R ω) xList)

theorem relativeEdgeDensity_zero_shift {Ω : Type*} [Fintype Ω]
    (w : FiniteLaw Ω) (N : ℕ) (R : Ω → ℕ → List ℕ) (xList : List ℕ) :
    relativeEdgeDensity w N R xList (fun _ => 0) = edgeDensity w N R xList := by
  simp only [relativeEdgeDensity, edgeDensity, edgeProbability,
    relativeInternalEdges_zero_shift]

theorem relativeEdgeDensity_eq_expected_shared_internal_edges {Ω : Type*} [Fintype Ω]
    (w : FiniteLaw Ω) (N : ℕ) (R : Ω → ℕ → List ℕ) (xList : List ℕ)
    (shift : Ω → ℕ) :
    relativeEdgeDensity w N R xList shift =
      (w.prod w).expectation (fun z =>
        ((relativeInternalEdges N (R z.1) xList (shift z.1) ∩
          relativeInternalEdges N (R z.2) xList (shift z.2)).card : ℝ)) := by
  simpa only [relativeEdgeDensity, pow_two] using
    (w.expected_card_intersection w (Finset.range (N - 1))
      (fun ω => relativeInternalEdges N (R ω) xList (shift ω))
      (fun ω => relativeInternalEdges N (R ω) xList (shift ω))
      (fun ω => relativeInternalEdges_subset_range N (R ω) xList (shift ω))
      (fun ω => relativeInternalEdges_subset_range N (R ω) xList (shift ω))).symm

theorem matrix_relative_density_le_mean_tail_fourth {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) (shift : FixedMatrix N n → ℕ) :
    relativeEdgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) shift ≤
      (prefixMean N n hM x) ^ 4 * (tailCollisionFactor N n M) ^ 2 / 4 := by
  have he : 0 ≤ (matrixLaw n hn).expectation
      (fun ω => (edgeCount N (sortedRows n ω) (prefixWord x) : ℝ)) :=
    (matrixLaw n hn).expectation_nonneg _ (fun _ => Nat.cast_nonneg _)
  have hb := matrix_expected_internal_edges_le_half_mean_bound n hn hM x
  calc
    _ ≤ ((matrixLaw n hn).expectation
        (fun ω => (edgeCount N (sortedRows n ω) (prefixWord x) : ℝ))) ^ 2 :=
      relative_density_le_sq_expected_absolute_edges
        (matrixLaw n hn) N (sortedRows n) (prefixWord x) shift
    _ ≤ ((prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M / 2) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hb hb he (le_trans he hb)
    _ = _ := by ring

theorem matrix_relative_density_le_prefixMean {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) (shift : FixedMatrix N n → ℕ) :
    relativeEdgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) shift ≤
      prefixMean N n hM x := by
  calc
    _ ≤ (matrixLaw n hn).expectation
        (fun ω => (occupancyCount N (sortedRows n ω) (prefixWord x) : ℝ)) :=
      relative_density_le_expected_occupancy
        (matrixLaw n hn) N (sortedRows n) (prefixWord x) shift
    _ = _ := matrix_expected_sorted_occupancy n hn hM x

end EdgeLocalization
