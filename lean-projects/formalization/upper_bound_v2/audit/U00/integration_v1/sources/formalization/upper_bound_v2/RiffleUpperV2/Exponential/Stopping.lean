import RiffleUpperV2.Exponential.Pathwise
import RiffleUpperV2.Exponential.Conditioning

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exponential

variable {Ω H : Type*}

/-- The good events up to and including the current revealed time. -/
def goodPrefix (B : ℕ → Ω → Prop) (i : ℕ) (ω : Ω) : Prop := ∀ j ≤ i, B j ω

/-- The multiplier is at time j+1, and is not required to be predictable at time j. -/
def stoppedProcess (X : ℕ → Ω → ℕ) (B : ℕ → Ω → Prop) (i : ℕ) (ω : Ω) : ℕ :=
  ∑ j ∈ Finset.range i, if goodPrefix B (j+1) ω then X (j+1) ω - X j ω else 0

@[simp] theorem stoppedProcess_zero (X : ℕ → Ω → ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    stoppedProcess X B 0 ω = 0 := by simp [stoppedProcess]

theorem goodPrefix_mono {B : ℕ → Ω → Prop} {i j : ℕ} {ω : Ω}
    (hij : i ≤ j) (h : goodPrefix B j ω) : goodPrefix B i ω :=
  fun a ha => h a (ha.trans hij)

theorem stoppedProcess_succ (X : ℕ → Ω → ℕ) (B : ℕ → Ω → Prop) (i : ℕ) (ω : Ω) :
    stoppedProcess X B (i+1) ω = stoppedProcess X B i ω +
      if goodPrefix B (i+1) ω then X (i+1) ω - X i ω else 0 := by
  exact Finset.sum_range_succ _ _

theorem stoppedProcess_increment (X : ℕ → Ω → ℕ) (B : ℕ → Ω → Prop) (i : ℕ) (ω : Ω) :
    stoppedProcess X B (i+1) ω - stoppedProcess X B i ω =
      if goodPrefix B (i+1) ω then X (i+1) ω - X i ω else 0 := by
  rw [stoppedProcess_succ, Nat.add_sub_cancel_left]

theorem stoppedProcess_unit {X : ℕ → Ω → ℕ} (B : ℕ → Ω → Prop) {m : ℕ}
    (hX : ∀ ω, UnitIncrements (fun i => X i ω) m) (ω : Ω) :
    UnitIncrements (fun i => stoppedProcess X B i ω) m := by
  intro j hj
  change stoppedProcess X B (j+1) ω = stoppedProcess X B j ω ∨
    stoppedProcess X B (j+1) ω = stoppedProcess X B j ω + 1
  rw [stoppedProcess_succ]
  by_cases hb : goodPrefix B (j+1) ω
  · simp only [hb, if_true]
    rcases hX ω j hj with h | h
    · left; simp [h]
    · right; simp [h]
  · left; simp [hb]

/-- The stopping event uses only the current history. -/
theorem goodPrefix_adapted {h : ℕ → Ω → H} {m : ℕ} (href : Refining h m)
    (B : ℕ → Ω → Prop)
    (hB : ∀ i ≤ m, HistoryMeasurable (h i) (B i)) {i : ℕ} (hi : i ≤ m) :
    HistoryMeasurable (h i) (goodPrefix B i) := by
  intro ω v hωv
  apply propext
  constructor <;> intro hb j hj
  · exact (hB j (hj.trans hi) ω v (href j i hj hi ω v hωv)) ▸ hb j hj
  · exact (hB j (hj.trans hi) ω v (href j i hj hi ω v hωv)).symm ▸ hb j hj

/-- Adaptation holds although the stopping multiplier is not predictable. -/
theorem stoppedProcess_adapted {h : ℕ → Ω → H} {m : ℕ} (href : Refining h m)
    (X : ℕ → Ω → ℕ) (B : ℕ → Ω → Prop)
    (hX : ∀ i ≤ m, HistoryMeasurable (h i) (X i))
    (hB : ∀ i ≤ m, HistoryMeasurable (h i) (B i)) {i : ℕ} (hi : i ≤ m) :
    HistoryMeasurable (h i) (stoppedProcess X B i) := by
  intro ω v hv
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j + 1 ≤ i := Finset.mem_range.mp hj
  have h1 := href (j+1) i hji hi ω v hv
  have h0 := href j i (by omega) hi ω v hv
  have hb := goodPrefix_adapted href B hB (hji.trans hi) ω v h1
  rw [hb, hX (j+1) (hji.trans hi) ω v h1, hX j (by omega) ω v h0]

/-- Source stopped-tail domination. The initial good event B_0 is included. -/
theorem stoppedProcess_tail_le {X : ℕ → Ω → ℕ} (B : ℕ → Ω → Prop) {m i : ℕ}
    (hX : ∀ ω, UnitIncrements (fun j => X j ω) m) (hi : i ≤ m) (ω : Ω) :
    stoppedProcess X B m ω - stoppedProcess X B i ω ≤
      if goodPrefix B i ω then X m ω - X i ω else 0 := by
  rw [← unit_increment_sum (stoppedProcess_unit B hX ω) hi]
  simp_rw [stoppedProcess_increment]
  by_cases hb : goodPrefix B i ω
  · simp only [hb, if_true]
    rw [← unit_increment_sum (hX ω) hi]
    apply Finset.sum_le_sum
    intro j hj
    split_ifs <;> omega
  · simp only [hb, if_false]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j hj
    have hij : i ≤ j+1 := by have := (Finset.mem_Ico.mp hj).1; omega
    have hb' : ¬ goodPrefix B (j+1) ω := fun h => hb (goodPrefix_mono hij h)
    simp [hb']

/-- On the final intersection the stopped process agrees with the original process. -/
theorem stoppedProcess_eq_on_good {X : ℕ → Ω → ℕ} {B : ℕ → Ω → Prop} {m : ℕ}
    (hX : ∀ ω, UnitIncrements (fun j => X j ω) m) (hzero : ∀ ω, X 0 ω = 0)
    (ω : Ω) (hb : goodPrefix B m ω) : stoppedProcess X B m ω = X m ω := by
  have he : stoppedProcess X B m ω = ∑ j ∈ Finset.Ico 0 m, (X (j+1) ω - X j ω) := by
    simp only [stoppedProcess, Nat.Ico_zero_eq_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j+1 ≤ m := Finset.mem_range.mp hj
    simp only [goodPrefix_mono hjm hb, if_true]
  rw [he, unit_increment_sum (hX ω) (Nat.zero_le m), hzero, Nat.sub_zero]

end RiffleUpperV2.Exponential
