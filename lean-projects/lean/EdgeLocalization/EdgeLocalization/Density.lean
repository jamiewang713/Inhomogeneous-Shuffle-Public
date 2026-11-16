import EdgeLocalization.FiniteLaw
import EdgeLocalization.Deck

/-! Frozen finite density consequences F22–F25.
These statements end at expected counts. They do not assert a tail-collision
product formula or an asymptotic exponent estimate. -/

noncomputable section

namespace EdgeLocalization

variable {Ω : Type*} [Fintype Ω]

def edgeProbability (w : FiniteLaw Ω) (N : ℕ)
    (R : Ω → ℕ → List ℕ) (x : List ℕ) (i : ℕ) : ℝ :=
  w.probability (fun ω => i ∈ internalEdges N (R ω) x)

def edgeDensity (w : FiniteLaw Ω) (N : ℕ)
    (R : Ω → ℕ → List ℕ) (x : List ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N - 1), (edgeProbability w N R x i) ^ 2

theorem internal_density_le_expected_edges (w : FiniteLaw Ω) (N : ℕ)
    (R : Ω → ℕ → List ℕ) (x : List ℕ) :
    edgeDensity w N R x ≤ w.expectation (fun ω => (edgeCount N (R ω) x : ℝ)) := by
  exact w.sum_sq_probabilities_le_expected_card (Finset.range (N - 1))
    (fun ω => internalEdges N (R ω) x)
    (fun ω => internalEdges_subset_range N (R ω) x)

theorem internal_density_le_expected_occupancy (w : FiniteLaw Ω) (N : ℕ)
    (R : Ω → ℕ → List ℕ) (x : List ℕ) :
    edgeDensity w N R x ≤ w.expectation (fun ω => (occupancyCount N (R ω) x : ℝ)) := by
  calc
    edgeDensity w N R x ≤ w.expectation (fun ω => (edgeCount N (R ω) x : ℝ)) :=
      internal_density_le_expected_edges w N R x
    _ ≤ _ := by
      apply w.expectation_mono
      intro ω
      exact_mod_cast internalEdges_card_le_occupancy N (R ω) x

theorem internal_expected_edges_le_expected_collisionPairs (w : FiniteLaw Ω) (N : ℕ)
    (R : Ω → ℕ → List ℕ) (x : List ℕ) :
    w.expectation (fun ω => (edgeCount N (R ω) x : ℝ)) ≤
      w.expectation (fun ω => ((collisionPairs N (R ω) x).card : ℝ)) := by
  apply w.expectation_mono
  intro ω
  exact_mod_cast internalEdges_card_le_collisionPairs N (R ω) x

theorem internal_density_le_expected_collisionPairs (w : FiniteLaw Ω) (N : ℕ)
    (R : Ω → ℕ → List ℕ) (x : List ℕ) :
    edgeDensity w N R x ≤
      w.expectation (fun ω => ((collisionPairs N (R ω) x).card : ℝ)) := by
  exact le_trans (internal_density_le_expected_edges w N R x)
    (internal_expected_edges_le_expected_collisionPairs w N R x)

end EdgeLocalization
