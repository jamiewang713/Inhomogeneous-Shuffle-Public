import Shuffle.HypergeometricMoments

noncomputable section
open scoped BigOperators

namespace Shuffle
namespace HypergeomParams

theorem weight_full_draw (p : HypergeomParams) (h : p.draws = p.population)
    (q : Fin (p.draws + 1)) : p.weight q = if q.val = p.marked then 1 else 0 := by
  by_cases hq : q.val = p.marked
  · simp [weight, h, hq]
  · simp only [hq, ↓reduceIte]
    by_cases hk : p.marked < q.val
    · simp [weight, Nat.choose_eq_zero_of_lt hk]
    · have hu : p.population - p.marked < p.draws - q.val := by
        have := p.marked_le
        omega
      simp [weight, Nat.choose_eq_zero_of_lt hu]

theorem expect_full_draw (p : HypergeomParams) (h : p.draws = p.population)
    (f : ℕ → ℝ) : p.law.expect (fun q => f q.val) = f p.marked := by
  classical
  let q0 : Fin (p.draws + 1) := ⟨p.marked, by have := p.marked_le; omega⟩
  have hq : ∀ q : Fin (p.draws + 1), q.val = p.marked ↔ q = q0 := by
    intro q
    exact ⟨fun he => Fin.ext he, fun he => congrArg Fin.val he⟩
  simp only [FiniteLaw.expect, law_mass, p.weight_full_draw h]
  simp [hq, q0]

theorem weight_marked_zero (p : HypergeomParams) (h : p.marked = 0)
    (q : Fin (p.draws + 1)) : p.weight q = if q.val = 0 then 1 else 0 := by
  by_cases hq : q.val = 0
  · simp [weight, h, hq, ne_of_gt p.denominator_pos]
  · simp [weight, h, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hq), hq]

theorem weight_full_marked (p : HypergeomParams) (h : p.marked = p.population)
    (q : Fin (p.draws + 1)) : p.weight q = if q.val = p.draws then 1 else 0 := by
  by_cases hq : q.val = p.draws
  · simp [weight, h, hq, ne_of_gt p.denominator_pos]
  · have hlt : 0 < p.draws - q.val := by omega
    simp [weight, h, Nat.choose_eq_zero_of_lt hlt, hq]

theorem expect_marked_zero (p : HypergeomParams) (h : p.marked = 0)
    (f : ℕ → ℝ) : p.law.expect (fun q => f q.val) = f 0 := by
  classical
  have hq : ∀ q : Fin (p.draws + 1), q.val = 0 ↔ q = 0 := by
    intro q
    exact ⟨fun he => Fin.ext he, fun he => congrArg Fin.val he⟩
  simp only [FiniteLaw.expect, law_mass, p.weight_marked_zero h]
  simp [hq]

theorem expect_full_marked (p : HypergeomParams) (h : p.marked = p.population)
    (f : ℕ → ℝ) : p.law.expect (fun q => f q.val) = f p.draws := by
  classical
  let q0 : Fin (p.draws + 1) := ⟨p.draws, Nat.lt_succ_self _⟩
  have hq : ∀ q : Fin (p.draws + 1), q.val = p.draws ↔ q = q0 := by
    intro q
    exact ⟨fun he => Fin.ext he, fun he => congrArg Fin.val he⟩
  simp only [FiniteLaw.expect, law_mass, p.weight_full_marked h]
  simp [hq, q0]

theorem expect_draws_zero (p : HypergeomParams) (h : p.draws = 0)
    (f : ℕ → ℝ) : p.law.expect (fun q => f q.val) = f 0 := by
  have hfun : (fun q : Fin (p.draws + 1) => f q.val) = fun _ => f 0 := by
    funext q
    have hq : q.val = 0 := by omega
    rw [hq]
  rw [hfun, p.law.expect_const]

theorem pointMass_full_draw (p : HypergeomParams) (h : p.draws = p.population)
    (q : ℕ) : p.pointMass q = if p.marked = q then 1 else 0 := by
  classical
  have hx := p.expect_full_draw h (fun n => if n = q then 1 else 0)
  have hp : p.pointMass q = p.law.expect (fun x => if x.val = q then 1 else 0) := by
    unfold pointMass FiniteLaw.prob FiniteLaw.expect
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x.val = q <;> simp [hx]
  exact hp.trans hx

private theorem pointMass_indicator (p : HypergeomParams) (q : ℕ) :
    p.pointMass q = p.law.expect (fun x => if x.val = q then 1 else 0) := by
  classical
  unfold pointMass FiniteLaw.prob FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x.val = q <;> simp [hx]

theorem pointMass_marked_zero (p : HypergeomParams) (h : p.marked = 0)
    (q : ℕ) : p.pointMass q = if 0 = q then 1 else 0 :=
  (pointMass_indicator p q).trans
    (p.expect_marked_zero h (fun n => if n = q then 1 else 0))

theorem pointMass_draws_zero (p : HypergeomParams) (h : p.draws = 0)
    (q : ℕ) : p.pointMass q = if 0 = q then 1 else 0 :=
  (pointMass_indicator p q).trans
    (p.expect_draws_zero h (fun n => if n = q then 1 else 0))

theorem pointMass_full_marked (p : HypergeomParams) (h : p.marked = p.population)
    (q : ℕ) : p.pointMass q = if p.draws = q then 1 else 0 :=
  (pointMass_indicator p q).trans
    (p.expect_full_marked h (fun n => if n = q then 1 else 0))

/-- H4's deterministic branch, including empty populations and zero draws. -/
theorem deterministic_of_variance_eq_zero (p : HypergeomParams)
    (hv : p.varianceFormula = 0) :
    ∃ q : ℕ, ∀ r : ℕ, p.pointMass r = if q = r then 1 else 0 := by
  have hv' : p.law.variance (fun q => (q.val : ℝ)) = 0 := by
    rw [p.variance_val, hv]
  rcases p.variance_eq_zero_iff.mp hv' with h | h | h | h
  · exact ⟨0, p.pointMass_marked_zero h⟩
  · exact ⟨0, p.pointMass_draws_zero h⟩
  · exact ⟨p.draws, p.pointMass_full_marked h⟩
  · exact ⟨p.marked, p.pointMass_full_draw h⟩

theorem centered_tail_zero (p : HypergeomParams)
    (hv : p.varianceFormula = 0) {t : ℝ} (ht : 0 < t) :
    p.law.prob (fun q => t ≤ |(q.val : ℝ) - p.mean|) = 0 := by
  apply le_antisymm _ (p.law.prob_nonneg _)
  have h := p.law.chebyshev (fun q => (q.val : ℝ)) ht
  simpa [p.expect_val, p.variance_val, hv] using h

end HypergeomParams
end Shuffle
