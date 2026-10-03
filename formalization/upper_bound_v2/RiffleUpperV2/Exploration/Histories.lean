import RiffleUpperV2.Exploration.Objects

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration

@[simp] theorem naturalHistory_zero {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (ω : Sample cuts) :
    naturalHistory cuts p d 0 ω = fun _ => none := by
  funext r
  simp [naturalHistory]

/-- Equality of later histories implies equality of earlier histories. -/
theorem history_refinement {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) {i j : ℕ} (hij : i ≤ j) {ω v : Sample cuts}
    (h : naturalHistory cuts p d j ω = naturalHistory cuts p d j v) :
    naturalHistory cuts p d i ω = naturalHistory cuts p d i v := by
  funext r
  have hr := congrFun h r
  by_cases hi : r.val < i
  · have hj : r.val < j := hi.trans_le hij
    simpa [naturalHistory, hi, hj] using hr
  · simp [naturalHistory, hi]

theorem revealed_word_eq {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) {ω v : Sample cuts}
    (h : naturalHistory cuts p d i ω = naturalHistory cuts p d i v)
    (r : Fin (pileSize cuts p)) (hr : r.val < i) :
    sortedWord ω (pilePosition cuts p d r) = sortedWord v (pilePosition cuts p d r) := by
  have hh := congrFun h r
  simpa [naturalHistory, hr] using hh

theorem historyFiber_eq {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) {ω v : Sample cuts}
    (h : naturalHistory cuts p d i ω = naturalHistory cuts p d i v) :
    historyFiber cuts p d i ω = historyFiber cuts p d i v := by
  funext z
  simp only [historyFiber, h]

theorem historyGood_adapted {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ ε : ℝ) (p : Fin k) (d : Direction) (i : ℕ) {ω v : Sample cuts}
    (h : naturalHistory cuts p d i ω = naturalHistory cuts p d i v) :
    historyGood cuts D g ξ ε p d i ω ↔ historyGood cuts D g ξ ε p d i v := by
  unfold historyGood
  rw [historyFiber_eq cuts p d i h]

/-- Every realized natural history has positive mass under the actual uniform fixed-column law. -/
theorem naturalHistory_positive {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) (ω : Sample cuts) :
    positiveHistory cuts p d i ω := by
  change 0 < ∑ v : Sample cuts, ((fixedCountPMF cuts) v).toReal *
    (if historyFiber cuts p d i ω v then (1 : ℝ) else 0)
  apply Finset.sum_pos'
  · intro v _
    positivity
  · refine ⟨ω, Finset.mem_univ _, ?_⟩
    have hf : historyFiber cuts p d i ω ω := rfl
    simp only [hf, if_true, mul_one]
    change 0 < ((PMF.uniformOfFintype (Sample cuts)) ω).toReal
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

/-- Equality on a null fiber is interpreted by the established zero-denominator convention. -/
theorem historyGood_of_null {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ ε : ℝ) (hε : 0 ≤ ε) (p : Fin k) (d : Direction) (i : ℕ)
    (ω : Sample cuts) (h : probability (fixedCountPMF cuts) (historyFiber cuts p d i ω) = 0) :
    historyGood cuts D g ξ ε p d i ω := by
  simp [historyGood, RiffleLowerV2.conditionalProbability, h, hε]

end RiffleUpperV2.Exploration
