import Mathlib.Tactic

namespace EdgeLocalization

/-- The number of digits strictly to the left of the middle digit. -/
def leftCount {N : ℕ} (c : Fin N → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => c i < 1).card

/-- The number of middle digits. -/
def middleCount {N : ℕ} (c : Fin N → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => c i = 1).card

/-- The number of digits strictly to the right of the middle digit. -/
def rightCount {N : ℕ} (c : Fin N → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => 1 < c i).card

/-- The zero-based lower endpoint of the one-digit middle cylinder. -/
def lowerEndpoint {N : ℕ} (c : Fin N → Fin 3) : ℕ :=
  leftCount c

/-- The zero-based upper endpoint of the one-digit middle cylinder. -/
def upperEndpoint {N : ℕ} (c : Fin N → Fin 3) : ℕ :=
  leftCount c + middleCount c

/-- Fixed column counts, with equal outer piles. -/
def BalancedColumn (a b : ℕ) :=
  {c : Fin (2 * a + b) → Fin 3 //
    leftCount c = a ∧ middleCount c = b ∧ rightCount c = a}

/-- D7's finite enumeration is derived from the finite column subtype. -/
instance balancedColumnFintype (a b : ℕ) : Fintype (BalancedColumn a b) := by
  unfold BalancedColumn
  infer_instance

/-- F26: the canonical three consecutive piles exist for all sizes. -/
theorem balanced_column_exists (a b : ℕ) : Nonempty (BalancedColumn a b) := by
  let c : Fin (2 * a + b) → Fin 3 := fun i =>
    if i.val < a then 0 else if i.val < a + b then 1 else 2
  have hleft (i : Fin (2 * a + b)) : c i < 1 ↔ i.val < a := by
    by_cases h₀ : i.val < a
    · simp [c, h₀]
    · by_cases h₁ : i.val < a + b
      · simp [c, h₀, h₁]
      · simp [c, h₀, h₁]
  have hmiddle (i : Fin (2 * a + b)) :
      c i = 1 ↔ a ≤ i.val ∧ i.val < a + b := by
    by_cases h₀ : i.val < a
    · have hn : ¬a ≤ i.val := by omega
      simp [c, h₀, hn]
    · have ha : a ≤ i.val := by omega
      by_cases h₁ : i.val < a + b
      · simp [c, h₀, h₁, ha]
      · simp [c, h₀, h₁, ha]
  have hright (i : Fin (2 * a + b)) : 1 < c i ↔ a + b ≤ i.val := by
    by_cases h₀ : i.val < a
    · have hn : ¬a + b ≤ i.val := by omega
      simp [c, h₀, hn]
    · by_cases h₁ : i.val < a + b
      · have hn : ¬a + b ≤ i.val := by omega
        simp [c, h₀, h₁, hn]
      · have ha : a + b ≤ i.val := by omega
        simp [c, h₀, h₁, ha]
  have hl : leftCount c = a := by
    unfold leftCount
    calc
      _ = (Finset.range a).card := by
        apply Finset.card_bij (fun i _ => i.val)
        · intro i hi
          exact Finset.mem_range.mpr ((hleft i).mp (Finset.mem_filter.mp hi).2)
        · intro i hi j hj hij
          exact Fin.ext hij
        · intro j hj
          have hj' : j < a := Finset.mem_range.mp hj
          let i : Fin (2 * a + b) := ⟨j, by omega⟩
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, rfl⟩
          exact (hleft i).mpr hj'
      _ = a := Finset.card_range a
  have hm : middleCount c = b := by
    unfold middleCount
    calc
      _ = (Finset.range b).card := by
        apply Finset.card_bij (fun i _ => i.val - a)
        · intro i hi
          have hi' := (hmiddle i).mp (Finset.mem_filter.mp hi).2
          apply Finset.mem_range.mpr
          omega
        · intro i hi j hj hij
          have hi' := (hmiddle i).mp (Finset.mem_filter.mp hi).2
          have hj' := (hmiddle j).mp (Finset.mem_filter.mp hj).2
          apply Fin.ext
          omega
        · intro j hj
          have hj' : j < b := Finset.mem_range.mp hj
          let i : Fin (2 * a + b) := ⟨a + j, by omega⟩
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, ?_⟩
          · apply (hmiddle i).mpr
            dsimp [i]
            omega
          · dsimp [i]
            omega
      _ = b := Finset.card_range b
  have hr : rightCount c = a := by
    unfold rightCount
    calc
      _ = (Finset.range a).card := by
        apply Finset.card_bij (fun i _ => i.val - (a + b))
        · intro i hi
          have hi' := (hright i).mp (Finset.mem_filter.mp hi).2
          have hiN := i.isLt
          apply Finset.mem_range.mpr
          omega
        · intro i hi j hj hij
          have hi' := (hright i).mp (Finset.mem_filter.mp hi).2
          have hj' := (hright j).mp (Finset.mem_filter.mp hj).2
          apply Fin.ext
          omega
        · intro j hj
          have hj' : j < a := Finset.mem_range.mp hj
          let i : Fin (2 * a + b) := ⟨a + b + j, by omega⟩
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, ?_⟩
          · apply (hright i).mpr
            dsimp [i]
            omega
          · dsimp [i]
            omega
      _ = a := Finset.card_range a
  exact ⟨⟨c, hl, hm, hr⟩⟩

/-- F27: fixing the column counts fixes the lower endpoint. -/
theorem balanced_left_endpoint {a b : ℕ} (c : BalancedColumn a b) :
    lowerEndpoint c.val = a := by
  exact c.property.1

/-- F28: fixing the column counts fixes the upper endpoint. -/
theorem balanced_right_endpoint {a b : ℕ} (c : BalancedColumn a b) :
    upperEndpoint c.val = a + b := by
  unfold upperEndpoint
  rw [c.property.1, c.property.2.1]

/-- F31: positive mass on both sides does not prevent a full residual sample. -/
theorem positive_side_mass_no_sampling_slack {a b : ℕ}
    (ha : 0 < a) (c : BalancedColumn a b) :
    (leftCount c.val = a ∧ 0 < leftCount c.val) ∧
    (rightCount c.val = a ∧ 0 < rightCount c.val) ∧
    1 - (2 * (a : ℝ)) / (2 * (a : ℝ)) = 0 := by
  refine ⟨⟨c.property.1, ?_⟩, ⟨c.property.2.2, ?_⟩, ?_⟩
  · rw [c.property.1]
    exact ha
  · rw [c.property.2.2]
    exact ha
  · have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hden : 2 * (a : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num) haR)
    rw [div_self hden, sub_self]

/-- F32: drawing the full population makes the variance numerator zero. -/
theorem full_sample_variance_numerator_zero (n n1 : ℕ) :
    n1 * n * (n - n1) * (n - n) = 0 := by
  simp

end EdgeLocalization
