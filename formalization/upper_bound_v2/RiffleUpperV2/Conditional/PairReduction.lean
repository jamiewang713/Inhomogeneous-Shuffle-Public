import RiffleUpperV2.Conditional.Jensen
import RiffleUpperV2.Shared.PairConditioning
import RiffleUpperV2.Exploration.Processes

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance 2000] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open Exploration

/-- The unrevealed single-matrix event retains the crossing edge at time i. -/
def remainingEdgeEvent {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ)
    (g : ℝ) (p : Fin k) (d : Direction) (i : ℕ)
    (e : Fin (pileSize cuts p - 1)) (ω : Sample cuts) : Prop :=
  i ≤ e.val+1 ∧ directionalEdge cuts D g p d e ω

/-- Each single-history squared-edge probability sum is bounded separately. -/
def historySelfIntersection {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ)
    (g : ℝ) (p : Fin k) (d : Direction) (i : ℕ) (ω : Sample cuts) : ℝ :=
  ∑ e, (conditionalProbability (fixedCountPMF cuts)
    (remainingEdgeEvent cuts D g p d i e) (historyFiber cuts p d i ω))^2

theorem conditionalExpect_card {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : PMF Ω) (E : I → Ω → Prop) (H : Ω → Prop) :
    conditionalExpect P (fun ω => ((Finset.univ.filter fun e => E e ω).card : ℝ)) H =
      ∑ e, conditionalProbability P (E e) H := by
  unfold conditionalExpect RiffleLowerV2.conditionalExpect conditionalProbability
    RiffleLowerV2.conditionalProbability RiffleLowerV2.probability RiffleLowerV2.expect
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.mul_sum]
  by_cases hH : H ω
  · simp [hH]
  · simp [hH]

/-- Pair-history fibers are exactly separate single-history fibers. No
regularity or concentration event is included in either conditioning event. -/
theorem pairHistoryFiber_eq {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) (ω : Sample cuts × Sample cuts) :
    (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω) =
      (fun v : Sample cuts × Sample cuts =>
        historyFiber cuts p d i ω.1 v.1 ∧ historyFiber cuts p d i ω.2 v.2) := by
  funext v
  simp only [pairHistory, historyFiber, Prod.mk.injEq]

theorem positivePairHistory_iff {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) (ω : Sample cuts × Sample cuts) :
    0 < probability (independentPairLaw cuts)
        (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω) ↔
      positiveHistory cuts p d i ω.1 ∧ positiveHistory cuts p d i ω.2 := by
  rw [pairHistoryFiber_eq]
  exact uniformProductProbability_pos_iff _ _

/-- Exact conditional product expansion of the concrete directional remainder. -/
theorem remainingCommonEdges_eq_sum {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (i : ℕ)
    (hp : (n : ℝ)^ξ ≤ (pileSize cuts p : ℝ)) (ω : Sample cuts × Sample cuts) :
    conditionalExpect (independentPairLaw cuts)
      (fun v => (remainingDirectionalCount cuts D g ξ p d i v.1 v.2 : ℝ))
      (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω) =
      ∑ e, conditionalProbability (fixedCountPMF cuts)
          (remainingEdgeEvent cuts D g p d i e) (historyFiber cuts p d i ω.1) *
        conditionalProbability (fixedCountPMF cuts)
          (remainingEdgeEvent cuts D g p d i e) (historyFiber cuts p d i ω.2) := by
  have hr : (fun v : Sample cuts × Sample cuts =>
      (remainingDirectionalCount cuts D g ξ p d i v.1 v.2 : ℝ)) =
      (fun v => ((Finset.univ.filter fun e =>
        remainingEdgeEvent cuts D g p d i e v.1 ∧
          remainingEdgeEvent cuts D g p d i e v.2).card : ℝ)) := by
    funext v
    rw [remainingDirectionalCount_eq, if_pos hp]
    congr 2
    ext e
    simp [remainingEdgeEvent, and_assoc, and_left_comm]
  rw [hr]
  refine (conditionalExpect_card (independentPairLaw cuts)
    (fun e v => remainingEdgeEvent cuts D g p d i e v.1 ∧
      remainingEdgeEvent cuts D g p d i e v.2)
    (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω)).trans ?_
  rw [pairHistoryFiber_eq]
  apply Finset.sum_congr rfl
  intro e _
  exact uniformProductConditionalProbability _ _ _ _

/-- Source final cross-history reduction. Both observed histories retain
separate terms, including the possible current-run crossing edge. -/
theorem remainingCommonEdges_le_self {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (i : ℕ)
    (hp : (n : ℝ)^ξ ≤ (pileSize cuts p : ℝ)) (ω : Sample cuts × Sample cuts) :
    conditionalExpect (independentPairLaw cuts)
      (fun v => (remainingDirectionalCount cuts D g ξ p d i v.1 v.2 : ℝ))
      (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω) ≤
      (historySelfIntersection cuts D g p d i ω.1 +
        historySelfIntersection cuts D g p d i ω.2) / 2 := by
  rw [remainingCommonEdges_eq_sum cuts D g ξ p d i hp ω]
  exact crossHistorySquareBound _ _

end RiffleUpperV2.Conditional
