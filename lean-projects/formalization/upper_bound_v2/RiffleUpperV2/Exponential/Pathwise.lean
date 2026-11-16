import RiffleUpperV2.Shared.Conditioning
import RiffleLowerV2.Thinning.PMFTools

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exponential

/-- A count has genuinely nonnegative increments, each at most one. -/
def UnitIncrements (X : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ j < m, X (j+1) = X j ∨ X (j+1) = X j + 1

/-- Monotonicity is proved before any natural subtraction is used as an increment. -/
theorem UnitIncrements.monotone {X : ℕ → ℕ} {m : ℕ} (hX : UnitIncrements X m)
    {i j : ℕ} (hij : i ≤ j) (hjm : j ≤ m) : X i ≤ X j := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    have hj : j < m := by omega
    rcases hX j hj with h | h <;> omega

theorem UnitIncrements.increment_le_one {X : ℕ → ℕ} {m : ℕ}
    (hX : UnitIncrements X m) {j : ℕ} (hj : j < m) : X (j+1) - X j ≤ 1 := by
  rcases hX j hj with h | h <;> omega

/-- The binomial step identity uses the increment known at time j+1. -/
theorem unit_choose_step {X : ℕ → ℕ} {m j : ℕ}
    (hX : UnitIncrements X m) (hj : j < m) (r : ℕ) :
    ((X m - X j).choose (r+1) : ℝ) - ((X m - X (j+1)).choose (r+1) : ℝ) =
      (X (j+1) - X j : ℕ) * ((X m - X (j+1)).choose r : ℝ) := by
  have hm := hX.monotone (Nat.le_of_lt hj) (le_refl m)
  have hm' := hX.monotone (Nat.succ_le_of_lt hj) (le_refl m)
  change X (j+1) ≤ X m at hm'
  rcases hX j hj with heq | heq
  · simp [heq]
  · have hd : X m - X j = (X m - X (j+1)) + 1 := by omega
    have hi : X (j+1) - X j = 1 := by omega
    rw [hd, Nat.choose_succ_succ', Nat.cast_add, hi, Nat.cast_one, one_mul]
    ring

/-- The finite unit-increment binomial identity, with no probabilistic assumption. -/
theorem unit_binomial_identity {X : ℕ → ℕ} {m i : ℕ}
    (hX : UnitIncrements X m) (hi : i ≤ m) (r : ℕ) :
    ((X m - X i).choose (r+1) : ℝ) =
      ∑ j ∈ Finset.Ico i m, (X (j+1) - X j : ℕ) *
        ((X m - X (j+1)).choose r : ℝ) := by
  have hs := Finset.sum_Ico_sub (fun j => -((X m - X j).choose (r+1) : ℝ)) hi
  have he : (∑ j ∈ Finset.Ico i m, (-((X m - X (j+1)).choose (r+1) : ℝ) -
      -((X m - X j).choose (r+1) : ℝ))) =
      ∑ j ∈ Finset.Ico i m, (X (j+1) - X j : ℕ) *
        ((X m - X (j+1)).choose r : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [neg_sub_neg, unit_choose_step hX (Finset.mem_Ico.mp hj).2]
  rw [he] at hs
  simpa using hs.symm

/-- Exact real-valued telescoping of the nonnegative natural increments. -/
theorem unit_increment_sum {X : ℕ → ℕ} {m i : ℕ}
    (hX : UnitIncrements X m) (hi : i ≤ m) :
    (∑ j ∈ Finset.Ico i m, (X (j+1) - X j : ℕ)) = (X m - X i : ℕ) := by
  have hs := Finset.sum_Ico_sub (fun j => (X j : ℝ)) hi
  have he : (∑ j ∈ Finset.Ico i m, ((X (j+1) : ℝ) - (X j : ℝ))) =
      ∑ j ∈ Finset.Ico i m, ((X (j+1) - X j : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm := (Finset.mem_Ico.mp hj).2
    rw [Nat.cast_sub (hX.monotone (Nat.le_succ j) (by omega))]
  rw [he, ← Nat.cast_sub (hX.monotone hi le_rfl), ← Nat.cast_sum] at hs
  exact_mod_cast hs

/-- A unit-increment process started from zero cannot count more than elapsed time. -/
theorem unit_terminal_le {X : ℕ → ℕ} {m : ℕ} (hX : UnitIncrements X m) (hzero : X 0 = 0) :
    X m ≤ m := by
  have hi : ∀ i ≤ m, X i ≤ i := by
    intro i
    induction i with
    | zero => intro _; simp [hzero]
    | succ i ih =>
      intro him
      have hi' := ih (by omega)
      have hstep := hX i (by omega)
      change X (i+1) ≤ i+1
      rcases hstep with he | he <;> omega
  exact hi m le_rfl

end RiffleUpperV2.Exponential
