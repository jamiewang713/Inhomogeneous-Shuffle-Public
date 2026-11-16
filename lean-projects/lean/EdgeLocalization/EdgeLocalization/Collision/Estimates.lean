import EdgeLocalization.Density
import EdgeLocalization.Collision.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast

/-! Internal-edge estimates in the frozen collision contract. -/

noncomputable section

namespace EdgeLocalization

theorem internal_density_le_sq_expected_edges {Ω : Type*} [Fintype Ω]
    (w : FiniteLaw Ω) (N : ℕ) (R : Ω → ℕ → List ℕ) (xList : List ℕ) :
    edgeDensity w N R xList ≤
      (w.expectation (fun ω => (edgeCount N (R ω) xList : ℝ))) ^ 2 := by
  have hs : (∑ i ∈ Finset.range (N - 1), edgeProbability w N R xList i) =
      w.expectation (fun ω => (edgeCount N (R ω) xList : ℝ)) :=
    w.sum_probabilities_eq_expected_card (Finset.range (N - 1))
      (fun ω => internalEdges N (R ω) xList)
      (fun ω => internalEdges_subset_range N (R ω) xList)
  calc
    edgeDensity w N R xList ≤
        (∑ i ∈ Finset.range (N - 1), edgeProbability w N R xList i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg
        (fun i _ => w.probability_nonneg (fun ω => i ∈ internalEdges N (R ω) xList))
    _ = _ := congrArg (fun z : ℝ => z ^ 2) hs

theorem matrix_expected_collisionPairs_le_tight_mean_bound {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    (matrixLaw n hn).expectation
        (fun ω => ((collisionPairs N (sortedRows n ω) (prefixWord x)).card : ℝ)) ≤
      (((N - 1 : ℕ) : ℝ) / (2 * (N : ℝ))) *
        (prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M := by
  by_cases h0 : N = 0
  · subst N
    rw [matrix_expected_sorted_collisionPairs n hn hM x]
    simp
  by_cases h1 : N = 1
  · subst N
    rw [matrix_expected_sorted_collisionPairs n hn hM x]
    simp
  have hN : 2 ≤ N := by omega
  have hq := (tail_factors_nonneg N n M).1
  have hc : (0 : ℝ) ≤ (N.choose 2 : ℝ) := Nat.cast_nonneg _
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast h0
  calc
    _ = (N.choose 2 : ℝ) * prefixPairFactor N n hM x *
        tailCollisionFactor N n M :=
      matrix_expected_sorted_collisionPairs n hn hM x
    _ ≤ (N.choose 2 : ℝ) * (prefixMass N n hM x) ^ 2 *
        tailCollisionFactor N n M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (prefixPairFactor_le_prefixMass_sq n hn hM x hN) hc) hq
    _ = _ := by
      rw [Nat.cast_choose_two ℝ N, Nat.cast_sub (by omega : 1 ≤ N)]
      simp only [Nat.cast_one, prefixMean]
      field_simp [hNz]

theorem matrix_expected_collisionPairs_le_half_mean_bound {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    (matrixLaw n hn).expectation
        (fun ω => ((collisionPairs N (sortedRows n ω) (prefixWord x)).card : ℝ)) ≤
      (prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M / 2 := by
  have hcoef : (((N - 1 : ℕ) : ℝ) / (2 * (N : ℝ))) ≤ (1 / 2 : ℝ) := by
    by_cases h0 : N = 0
    · subst N
      norm_num
    · have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero h0)
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hN)).mpr
      have hsub : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.sub_le N 1
      nlinarith
  have hprod : 0 ≤ (prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M :=
    mul_nonneg (sq_nonneg _) (tail_factors_nonneg N n M).1
  calc
    _ ≤ (((N - 1 : ℕ) : ℝ) / (2 * (N : ℝ))) *
        (prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M :=
      matrix_expected_collisionPairs_le_tight_mean_bound n hn hM x
    _ = (((N - 1 : ℕ) : ℝ) / (2 * (N : ℝ))) *
        ((prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M) := by ring
    _ ≤ (1 / 2 : ℝ) *
        ((prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M) :=
      mul_le_mul_of_nonneg_right hcoef hprod
    _ = _ := by ring

theorem matrix_expected_internal_edges_le_half_mean_bound {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    (matrixLaw n hn).expectation
        (fun ω => (edgeCount N (sortedRows n ω) (prefixWord x) : ℝ)) ≤
      (prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M / 2 := by
  exact le_trans
    (internal_expected_edges_le_expected_collisionPairs
      (matrixLaw n hn) N (sortedRows n) (prefixWord x))
    (matrix_expected_collisionPairs_le_half_mean_bound n hn hM x)

theorem matrix_internal_density_le_collision_square {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
      ((N.choose 2 : ℝ) * prefixPairFactor N n hM x *
        tailCollisionFactor N n M) ^ 2 := by
  have he : 0 ≤ (matrixLaw n hn).expectation
      (fun ω => (edgeCount N (sortedRows n ω) (prefixWord x) : ℝ)) :=
    (matrixLaw n hn).expectation_nonneg _ (fun _ => Nat.cast_nonneg _)
  have hb := internal_expected_edges_le_expected_collisionPairs
    (matrixLaw n hn) N (sortedRows n) (prefixWord x)
  rw [matrix_expected_sorted_collisionPairs n hn hM x] at hb
  calc
    _ ≤ ((matrixLaw n hn).expectation
        (fun ω => (edgeCount N (sortedRows n ω) (prefixWord x) : ℝ))) ^ 2 :=
      internal_density_le_sq_expected_edges
        (matrixLaw n hn) N (sortedRows n) (prefixWord x)
    _ ≤ _ := by
      simpa only [pow_two] using mul_le_mul hb hb he (le_trans he hb)

theorem matrix_internal_density_le_mean_tail_fourth {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
      (prefixMean N n hM x) ^ 4 * (tailCollisionFactor N n M) ^ 2 / 4 := by
  have he : 0 ≤ (matrixLaw n hn).expectation
      (fun ω => (edgeCount N (sortedRows n ω) (prefixWord x) : ℝ)) :=
    (matrixLaw n hn).expectation_nonneg _ (fun _ => Nat.cast_nonneg _)
  have hb := matrix_expected_internal_edges_le_half_mean_bound n hn hM x
  calc
    _ ≤ ((matrixLaw n hn).expectation
        (fun ω => (edgeCount N (sortedRows n ω) (prefixWord x) : ℝ))) ^ 2 :=
      internal_density_le_sq_expected_edges
        (matrixLaw n hn) N (sortedRows n) (prefixWord x)
    _ ≤ ((prefixMean N n hM x) ^ 2 * tailCollisionFactor N n M / 2) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hb hb he (le_trans he hb)
    _ = _ := by ring

theorem matrix_internal_density_le_prefixMean {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
      prefixMean N n hM x := by
  calc
    _ ≤ (matrixLaw n hn).expectation
        (fun ω => (occupancyCount N (sortedRows n ω) (prefixWord x) : ℝ)) :=
      internal_density_le_expected_occupancy
        (matrixLaw n hn) N (sortedRows n) (prefixWord x)
    _ = _ := matrix_expected_sorted_occupancy n hn hM x

end EdgeLocalization
