import RiffleUpperV2.Reservoir.History
import RiffleUpperV2.Shared.Conditioning

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

/-- Residual column count after exposing exactly the unmarked rows of pile p.
All outside-pile rows and all marked rows remain available. -/
def remainingCount {k n L : ℕ} {cuts : Cuts k n (L+1)} (p : Fin k)
    (M : Finset (Fin n)) (j : Fin (L+1)) (a : Fin k) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun r : Fin n =>
    ((rowWord ω r).get 0 ≠ p ∨ r ∈ M) ∧ (rowWord ω r).get j = a).card

theorem remainingCount_eq {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (M : Finset (Fin n)) (ω : Sample cuts)
    (hM : ∀ r ∈ M, (rowWord ω r).get 0 = p) (j : Fin (L+1)) (a : Fin k) :
    remainingCount p M j a ω = outsideCount cuts p j a ω +
      (M.filter fun r => (rowWord ω r).get j = a).card := by
  let O := Finset.univ.filter fun r : Fin n =>
    (rowWord ω r).get 0 ≠ p ∧ (rowWord ω r).get j = a
  let Q := M.filter fun r => (rowWord ω r).get j = a
  have hd : Disjoint O Q := by
    apply Finset.disjoint_left.mpr
    intro r hr hq
    exact (Finset.mem_filter.mp hr).2.1 (hM r (Finset.mem_filter.mp hq).1)
  have he : Finset.univ.filter (fun r : Fin n =>
      ((rowWord ω r).get 0 ≠ p ∨ r ∈ M) ∧ (rowWord ω r).get j = a) = O ∪ Q := by
    ext r
    simp only [O, Q, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  exact (congrArg Finset.card he).trans (Finset.card_union_of_disjoint hd)

/-- The actual simultaneous event H implies the needed residual-count good
configuration for every marked set, with the exact additive |M| perturbation. -/
theorem concentration_remainingCount {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (M : Finset (Fin n)) (ω : Sample cuts)
    (hH : concentrationEvent cuts D g ξ ω)
    (hM : ∀ r ∈ M, (rowWord ω r).get 0 = p)
    (j : Fin (L+1)) (a : Fin k) (hj : 0 < j.val) :
    |(remainingCount p M j a ω : ℝ) -
        (n - pileSize cuts p : ℕ) * ((cuts.count j a : ℝ) / n)| ≤
      (n : ℝ)^((2:ℝ)/3) + M.card := by
  rw [remainingCount_eq cuts p M ω hM j a, Nat.cast_add]
  have ho := hH.1 p j a hj
  have hm : ((M.filter fun r => (rowWord ω r).get j = a).card : ℝ) ≤ M.card := by
    exact_mod_cast Finset.card_filter_le M (fun r => (rowWord ω r).get j = a)
  calc
    _ = |((outsideCount cuts p j a ω : ℝ) -
          (n - pileSize cuts p : ℕ) * ((cuts.count j a : ℝ) / n)) +
          (M.filter fun r => (rowWord ω r).get j = a).card| := by congr 1; ring
    _ ≤ |(outsideCount cuts p j a ω : ℝ) -
          (n - pileSize cuts p : ℕ) * ((cuts.count j a : ℝ) / n)| +
          |((M.filter fun r => (rowWord ω r).get j = a).card : ℝ)| := abs_add_le _ _
    _ ≤ (n : ℝ)^((2:ℝ)/3) + M.card := by
      have ha : |((M.filter fun r => (rowWord ω r).get j = a).card : ℝ)| =
          ((M.filter fun r => (rowWord ω r).get j = a).card : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [ha]
      exact add_le_add ho hm

/-- Only a copy whose deletion still leaves t copies is charged as fresh.
The t copies forced by the observed history never appear as an additive error. -/
theorem removableCopies {k n L : ℕ} (cuts : Cuts k n L) (ω : Sample cuts)
    (s : Word k L) (t : ℕ) :
    wordCount ω s - t ≤
      (Finset.univ.filter fun r : Fin n =>
        rowWord ω r = s ∧ t ≤ wordCount ω s - 1).card := by
  by_cases ht : t < wordCount ω s
  · have hh : t ≤ wordCount ω s - 1 := by omega
    have he : (Finset.univ.filter fun r : Fin n => rowWord ω r = s ∧
        t ≤ wordCount ω s - 1) = Finset.univ.filter (fun r => rowWord ω r = s) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hh, and_true]
    rw [he]
    exact Nat.sub_le _ _
  · have hz : wordCount ω s - t = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt ht)
    rw [hz]
    exact Nat.zero_le _

/-- The one bad-configuration event for a marked pair already includes every
possible equal completion. It is bounded once, before any word expansion. -/
theorem collision_bad_event_le {k n L : ℕ} (cuts : Cuts k n L)
    (r s : Fin n) (B H : Sample cuts → Prop) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => rowWord ω r = rowWord ω s ∧ B ω) H ≤
    conditionalProbability (fixedCountPMF cuts) B H := by
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  apply div_le_div_of_nonneg_right
  · unfold RiffleLowerV2.probability RiffleLowerV2.expect
    apply Finset.sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    dsimp only
    split_ifs <;> simp_all
  · unfold RiffleLowerV2.probability RiffleLowerV2.expect
    exact Finset.sum_nonneg (fun _ _ => by positivity)

end RiffleUpperV2.Reservoir
