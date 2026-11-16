import EdgeLocalization.Collision.Rows

/-! Exact independent-column formulas and scalar-factor comparisons from the
frozen additive collision contract. All probabilities use the constructed
fixed-column matrix law. -/

noncomputable section

namespace EdgeLocalization

open Finset

theorem matrixLaw_uniform_weight {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (hn : ∀ j, ∑ a, n j a = N) (ω : FixedMatrix N n) :
    (matrixLaw n hn).weight ω = (Fintype.card (FixedMatrix N n) : ℝ)⁻¹ := by
  classical
  change (∏ j, (Fintype.card (FixedColumn N k (n j)) : ℝ)⁻¹) = _
  rw [Finset.prod_inv_distrib]
  congr 1
  simp only [FixedMatrix, Fintype.card_pi, Nat.cast_prod]

theorem matrix_prefix_probability {N K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (x : Fin M → Fin k)
    (i : Fin N) :
    (matrixLaw n hn).probability (fun ω => prefixWord x <+: rawRow n ω i) =
      prefixMass N n hM x := by
  classical
  let s := Finset.univ.filter (fun j : Fin K => j.val < M)
  let A : ∀ j : Fin K, FixedColumn N k (n j) → Prop := fun j c =>
    if hj : j.val < M then c.val i = x ⟨j.val, hj⟩ else True
  have hevent (ω : FixedMatrix N n) :
      prefixWord x <+: rawRow n ω i ↔ ∀ j ∈ s, A j (ω j) := by
    rw [prefixWord_prefix_rawRow_iff n hM x ω i]
    constructor
    · intro h j hj
      have hjM : j.val < M := (Finset.mem_filter.mp hj).2
      have hc : Fin.castLE hM (⟨j.val, hjM⟩ : Fin M) = j := Fin.ext rfl
      simpa only [A, dif_pos hjM, hc] using h ⟨j.val, hjM⟩
    · intro h t
      have ht : (Fin.castLE hM t).val < M := t.isLt
      have hts : Fin.castLE hM t ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
      simpa only [A, dif_pos ht] using h (Fin.castLE hM t) hts
  calc
    _ = (matrixLaw n hn).probability (fun ω => ∀ j ∈ s, A j (ω j)) :=
      (matrixLaw n hn).probability_congr _ _ hevent
    _ = ∏ j ∈ s, (columnLaw (n j) (hn j)).probability (A j) :=
      FiniteLaw.pi_probability_on_finset
        (Ω := fun j : Fin K => FixedColumn N k (n j)) _ s A
    _ = prefixMass N n hM x := by
      unfold prefixMass
      refine Finset.prod_bij
        (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin M)) ?_ ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_univ _
      · intro j hj l hl h
        exact Fin.ext (congrArg (fun t : Fin M => t.val) h)
      · intro t ht
        refine ⟨Fin.castLE hM t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, ?_⟩
        exact Fin.ext rfl
      · intro j hj
        have hjM : j.val < M := (Finset.mem_filter.mp hj).2
        have hc : Fin.castLE hM (⟨j.val, hjM⟩ : Fin M) = j := Fin.ext rfl
        simpa only [A, dif_pos hjM, hc] using
          column_one_probability (n j) (hn j) i (x ⟨j.val, hjM⟩)

theorem matrix_pair_prefix_probability {N K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (x : Fin M → Fin k)
    (i l : Fin N) (hil : i ≠ l) :
    (matrixLaw n hn).probability
        (fun ω => rawRow n ω i = rawRow n ω l ∧ prefixWord x <+: rawRow n ω i) =
      prefixPairFactor N n hM x * tailCollisionFactor N n M := by
  classical
  let A : ∀ j : Fin K, FixedColumn N k (n j) → Prop := fun j c =>
    if hj : j.val < M then c.val i = x ⟨j.val, hj⟩ ∧ c.val l = x ⟨j.val, hj⟩
    else c.val i = c.val l
  let f : Fin K → ℝ := fun j => (columnLaw (n j) (hn j)).probability (A j)
  have hevent (ω : FixedMatrix N n) :
      (rawRow n ω i = rawRow n ω l ∧ prefixWord x <+: rawRow n ω i) ↔
        ∀ j, A j (ω j) := by
    rw [rawRow_eq_iff n ω i l, prefixWord_prefix_rawRow_iff n hM x ω i]
    constructor
    · rintro ⟨heq, hx⟩ j
      by_cases hj : j.val < M
      · have hc : Fin.castLE hM (⟨j.val, hj⟩ : Fin M) = j := Fin.ext rfl
        have hxi : (ω j).val i = x ⟨j.val, hj⟩ := by simpa only [hc] using hx ⟨j.val, hj⟩
        simpa only [A, dif_pos hj] using And.intro hxi ((heq j).symm.trans hxi)
      · simpa only [A, dif_neg hj] using heq j
    · intro h
      constructor
      · intro j
        by_cases hj : j.val < M
        · have hh : (ω j).val i = x ⟨j.val, hj⟩ ∧ (ω j).val l = x ⟨j.val, hj⟩ := by
            simpa only [A, dif_pos hj] using h j
          exact hh.1.trans hh.2.symm
        · simpa only [A, dif_neg hj] using h j
      · intro t
        have ht : (Fin.castLE hM t).val < M := t.isLt
        have hh : (ω (Fin.castLE hM t)).val i = x t ∧
            (ω (Fin.castLE hM t)).val l = x t := by
          simpa only [A, dif_pos ht] using h (Fin.castLE hM t)
        exact hh.1
  have hp :
      (∏ j ∈ Finset.univ.filter (fun j : Fin K => j.val < M), f j) =
        prefixPairFactor N n hM x := by
    unfold prefixPairFactor
    refine Finset.prod_bij
      (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin M)) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_univ _
    · intro j hj r hr h
      exact Fin.ext (congrArg (fun t : Fin M => t.val) h)
    · intro t ht
      refine ⟨Fin.castLE hM t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, ?_⟩
      exact Fin.ext rfl
    · intro j hj
      have hjM : j.val < M := (Finset.mem_filter.mp hj).2
      have hc : Fin.castLE hM (⟨j.val, hjM⟩ : Fin M) = j := Fin.ext rfl
      simpa only [f, A, dif_pos hjM, hc] using
        column_two_probability (n j) (hn j) i l hil (x ⟨j.val, hjM⟩) (x ⟨j.val, hjM⟩)
  have ht :
      (∏ j ∈ Finset.univ.filter (fun j : Fin K => ¬j.val < M), f j) =
        tailCollisionFactor N n M := by
    unfold tailCollisionFactor
    apply Finset.prod_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    · intro j hj
      have hjM : ¬j.val < M := Nat.not_lt.mpr (Finset.mem_filter.mp hj).2
      simpa only [f, A, dif_neg hjM] using column_equal_probability (n j) (hn j) i l hil
  calc
    _ = (matrixLaw n hn).probability (fun ω => ∀ j, A j (ω j)) :=
      (matrixLaw n hn).probability_congr _ _ hevent
    _ = ∏ j : Fin K, f j := FiniteLaw.pi_probability
      (Ω := fun j : Fin K => FixedColumn N k (n j)) _ A
    _ = _ := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun j : Fin K => j.val < M) f, hp, ht]

theorem matrix_expected_raw_occupancy {N K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (x : Fin M → Fin k) :
    (matrixLaw n hn).expectation
        (fun ω => (occupancyCount N (rawRows n ω) (prefixWord x) : ℝ)) =
      prefixMean N n hM x := by
  classical
  have hsum := (matrixLaw n hn).sum_probabilities_eq_expected_card (Finset.range N)
    (fun ω => occupied N (rawRows n ω) (prefixWord x))
    (fun ω => Finset.filter_subset _ _)
  calc
    _ = ∑ j ∈ Finset.range N, (matrixLaw n hn).probability
        (fun ω => j ∈ occupied N (rawRows n ω) (prefixWord x)) := hsum.symm
    _ = ∑ _j ∈ Finset.range N, prefixMass N n hM x := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      calc
        _ = (matrixLaw n hn).probability
            (fun ω => prefixWord x <+: rawRow n ω (⟨j, hjN⟩ : Fin N)) := by
          apply (matrixLaw n hn).probability_congr
          intro ω
          simp [occupied, rawRows, rowsOfLabels, hjN]
        _ = _ := matrix_prefix_probability n hn hM x ⟨j, hjN⟩
    _ = _ := by simp [prefixMean]

theorem matrix_expected_sorted_occupancy {N K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (x : Fin M → Fin k) :
    (matrixLaw n hn).expectation
        (fun ω => (occupancyCount N (sortedRows n ω) (prefixWord x) : ℝ)) =
      prefixMean N n hM x := by
  calc
    _ = (matrixLaw n hn).expectation
        (fun ω => (occupancyCount N (rawRows n ω) (prefixWord x) : ℝ)) := by
      congr 1
      funext ω
      rw [sorted_occupancy_eq_raw]
    _ = _ := matrix_expected_raw_occupancy n hn hM x

theorem matrix_expected_raw_collisionPairs {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    (matrixLaw n hn).expectation
        (fun ω => ((collisionPairs N (rawRows n ω) (prefixWord x)).card : ℝ)) =
      (Nat.choose N 2 : ℝ) * prefixPairFactor N n hM x * tailCollisionFactor N n M := by
  classical
  by_cases hzero : N = 0
  · subst N
    simp only [collisionPairs_zero, Finset.card_empty, Nat.cast_zero,
      Nat.choose_zero_succ, zero_mul]
    exact (matrixLaw n hn).expectation_const 0
  by_cases hone : N = 1
  · subst N
    have hc : Nat.choose 1 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [collisionPairs_one, Finset.card_empty, Nat.cast_zero, hc, zero_mul]
    exact (matrixLaw n hn).expectation_const 0
  let s := ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 < p.2)
  have hsum := (matrixLaw n hn).sum_probabilities_eq_expected_card s
    (fun ω => collisionPairs N (rawRows n ω) (prefixWord x))
    (fun ω => collisionPairs_subset_increasing N (rawRows n ω) (prefixWord x))
  calc
    _ = ∑ p ∈ s, (matrixLaw n hn).probability
        (fun ω => p ∈ collisionPairs N (rawRows n ω) (prefixWord x)) := hsum.symm
    _ = ∑ _p ∈ s, prefixPairFactor N n hM x * tailCollisionFactor N n M := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpN, hpLt⟩
      rcases Finset.mem_product.mp hpN with ⟨hi, hj⟩
      have hiN : p.1 < N := Finset.mem_range.mp hi
      have hjN : p.2 < N := Finset.mem_range.mp hj
      have hij : (⟨p.1, hiN⟩ : Fin N) ≠ ⟨p.2, hjN⟩ := by
        intro heq
        have hv := congrArg (fun t : Fin N => t.val) heq
        change p.1 = p.2 at hv
        omega
      calc
        _ = (matrixLaw n hn).probability
            (fun ω => rawRow n ω (⟨p.1, hiN⟩ : Fin N) = rawRow n ω ⟨p.2, hjN⟩ ∧
              prefixWord x <+: rawRow n ω ⟨p.1, hiN⟩) := by
          apply (matrixLaw n hn).probability_congr
          intro ω
          simp [collisionPairs, rawRows, rowsOfLabels, hiN, hjN, hpLt]
        _ = _ := matrix_pair_prefix_probability n hn hM x ⟨p.1, hiN⟩ ⟨p.2, hjN⟩ hij
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, s, increasing_pair_card, mul_assoc]

theorem matrix_expected_sorted_collisionPairs {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    (matrixLaw n hn).expectation
        (fun ω => ((collisionPairs N (sortedRows n ω) (prefixWord x)).card : ℝ)) =
      (Nat.choose N 2 : ℝ) * prefixPairFactor N n hM x * tailCollisionFactor N n M := by
  calc
    _ = (matrixLaw n hn).expectation
        (fun ω => ((collisionPairs N (rawRows n ω) (prefixWord x)).card : ℝ)) := by
      congr 1
      funext ω
      rw [sorted_collisionPairs_card_eq_raw]
    _ = _ := matrix_expected_raw_collisionPairs n hn hM x

theorem prefix_factors_nonneg (N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hM : M ≤ K) (x : Fin M → Fin k) :
    0 ≤ prefixMass N n hM x ∧ 0 ≤ prefixPairFactor N n hM x ∧
      0 ≤ prefixMean N n hM x := by
  have hp : 0 ≤ prefixMass N n hM x :=
    Finset.prod_nonneg (fun t _ => singleFactor_nonneg N _ _)
  have hq : 0 ≤ prefixPairFactor N n hM x :=
    Finset.prod_nonneg (fun t _ => pairFactor_nonneg N _ _ _)
  exact ⟨hp, hq, mul_nonneg (Nat.cast_nonneg _) hp⟩

theorem tail_factors_nonneg (N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ)
    (M : ℕ) : 0 ≤ tailCollisionFactor N n M ∧ 0 ≤ tailSquareFactor N n M := by
  constructor
  · exact Finset.prod_nonneg (fun j _ =>
      Finset.sum_nonneg (fun a _ => pairFactor_nonneg N _ _ _))
  · exact Finset.prod_nonneg (fun j _ => Finset.sum_nonneg (fun a _ => sq_nonneg _))

theorem prefixPairFactor_le_prefixMass_sq {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) (hN : 2 ≤ N) :
    prefixPairFactor N n hM x ≤ (prefixMass N n hM x) ^ 2 := by
  calc
    _ ≤ ∏ t : Fin M, (singleFactor N (n (Fin.castLE hM t)) (x t)) ^ 2 := by
      apply Finset.prod_le_prod
      · intro t _
        exact pairFactor_nonneg N _ _ _
      · intro t _
        exact pairFactor_same_le_singleFactor_sq N (n (Fin.castLE hM t))
          (hn (Fin.castLE hM t)) hN (x t)
    _ = _ := by rw [Finset.prod_pow]; rfl

theorem tailCollisionFactor_le_tailSquareFactor {N K k : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (M : ℕ) (hN : 2 ≤ N) :
    tailCollisionFactor N n M ≤ tailSquareFactor N n M := by
  apply Finset.prod_le_prod
  · intro j _
    exact Finset.sum_nonneg (fun a _ => pairFactor_nonneg N _ _ _)
  · intro j _
    apply Finset.sum_le_sum
    intro a _
    exact pairFactor_same_le_singleFactor_sq N (n j) (hn j) hN a

theorem tailCollisionFactor_at_full_length (N : ℕ) {K k : ℕ}
    (n : Fin K → Fin k → ℕ) : tailCollisionFactor N n K = 1 := by
  have h : (Finset.univ.filter (fun j : Fin K => K ≤ j.val)) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    exact Nat.not_le.mpr j.isLt
  simp only [tailCollisionFactor, h, Finset.prod_empty]

theorem prefix_factors_empty (N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ)
    (hM : 0 ≤ K) (x : Fin 0 → Fin k) :
    prefixWord x = [] ∧ prefixMass N n hM x = 1 ∧ prefixPairFactor N n hM x = 1 := by
  simp [prefixWord, prefixMass, prefixPairFactor]

end EdgeLocalization
