import RiffleLowerV2.Shared.Statistics

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2
open TimeProfile MeasureTheory

theorem expect_eq_integral {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : PMF Ω) (f : Ω → ℝ) :
    expect P f = ∫ ω, f ω ∂P.toMeasure := by
  rw [PMF.integral_eq_sum]
  simp [expect, smul_eq_mul]

theorem fixed_expect_eq_average {k N K : ℕ} (cuts : Cuts k N K) (f : Sample cuts → ℝ) :
    expect (fixedCountPMF cuts) f = (∑ ω, f ω) / Fintype.card (Sample cuts) := by
  rw [expect_eq_integral]
  exact fixedCount_integral_eq_average cuts f

theorem columnFraction_grid {K N : ℕ} (hN : 2 ≤ N) (j : Fin K) (m : ℕ) :
    columnFraction N j (gridTime N m) = if j.val < m then 1 else 0 := by
  have hL := (logScale_pos hN).ne'
  simp only [columnFraction, gridTime, div_mul_cancel₀ _ hL]
  by_cases hj : j.val < m
  · have hd : (1 : ℝ) ≤ (m : ℝ) - j.val := by
      have hc : (j.val : ℝ) + 1 ≤ m := by exact_mod_cast (show j.val + 1 ≤ m by omega)
      linarith
    simp [hj, min_eq_left hd]
  · have hd : (m : ℝ) - j.val ≤ 0 := by
      have hc : (m : ℝ) ≤ j.val := by exact_mod_cast (show m ≤ j.val by omega)
      linarith
    rw [min_eq_right (by linarith), max_eq_left hd, if_neg hj]

theorem empiricalIntegral_grid {K N : ℕ} (hN : 2 ≤ N) (f : Fin K → ℝ)
    (a b : ℕ) (hab : a ≤ b) :
    empiricalIntegral N f (gridTime N a) (gridTime N b) = gridSum N f a b := by
  classical
  simp only [empiricalIntegral, columnFraction_grid hN, gridSum, Finset.sum_div]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases ha : j.val < a
  · have hb : j.val < b := lt_of_lt_of_le ha hab
    simp [ha, hb, Nat.not_le.mpr ha]
  · by_cases hb : j.val < b
    · simp [ha, hb, Nat.le_of_not_gt ha]
    · simp [ha, hb]

@[simp] theorem emptyPrefix_mass {k N K : ℕ} (cuts : Cuts k N K) :
    prefixMass cuts ⟨⟨0, by omega⟩, RiffleShuffle.emptyWord k⟩ = 1 := by
  simp [prefixMass]

theorem matrix_graph_adapter {k N K : ℕ} {cuts : Cuts k N K}
    (hN : 0 < N) (hk : 2 ≤ k) (ω : Sample cuts) (e : Fin (N-1)) :
    e ∈ shuffleEdges ω ↔ (toMatrix hN hk ω).shuffleGraph.Adj (edgeLeft e) (edgeRight e) := by
  classical
  unfold shuffleEdges
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (sortedWord ω (edgeLeft e) = sortedWord ω (edgeRight e)) ↔ _
  simp [RiffleShuffle.ShuffleMatrix.shuffleGraph, sortedWord,
    RiffleShuffle.ShuffleMatrix.sortedRows, toMatrix, edgeLeft, edgeRight,
    RiffleShuffle.ShuffleMatrix.sortPerm, stableSort]

theorem clipTranslate_card_le (N : ℕ) (H0 : Finset ℤ) (q : ℤ) :
    (clipTranslate N H0 q).card ≤ H0.card := by
  apply Finset.card_le_card_of_injOn (fun i => manuscriptRank i - q)
  · intro i hi
    exact (mem_clipTranslate H0 q i).mp hi
  · intro i _ j _ hij
    apply Fin.ext
    dsimp [manuscriptRank] at hij
    omega

@[simp] theorem emptyPrefix_count {k N K : ℕ} {cuts : Cuts k N K} (ω : Sample cuts) :
    prefixCount ⟨⟨0, by omega⟩, RiffleShuffle.emptyWord k⟩ ω = N := by
  classical
  simp [prefixCount, RiffleShuffle.emptyWord]

end RiffleLowerV2
