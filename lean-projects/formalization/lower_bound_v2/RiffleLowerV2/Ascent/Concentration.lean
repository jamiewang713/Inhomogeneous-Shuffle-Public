import RiffleLowerV2.Ascent.Components
import RiffleLowerV2.Ascent.RelativeOrder.Law
import RiffleLowerV2.Ascent.MGF
import RiffleLowerV2.Ascent.FiniteConsequences

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Ascent

/-- Exact exponential factorization on one component-parity class. -/
theorem boundary_class_factorization {N : ℕ} (G : PathEdges N)
    (s : Finset (Fin (N-1))) (hs : ∀ e ∈ s, e ∉ G)
    (hp : ∀ e ∈ s, ∀ f ∈ s, boundaryParity G e = boundaryParity G f) (u : ℝ) :
    expect (uniformPermutation N) (fun π => ∏ e ∈ s,
      Real.exp (u * ((if boundaryAscent G e π then 1 else 0) -
        probability (uniformPermutation N) (boundaryAscent G e)))) =
      ∏ e ∈ s, expect (uniformPermutation N) (fun π =>
        Real.exp (u * ((if boundaryAscent G e π then 1 else 0) -
          probability (uniformPermutation N) (boundaryAscent G e)))) := by
  have h := expect_prod_of_relativeOrder
    (I := s) (fun e => boundarySupport G e.val)
    (fun e f hef => boundarySupport_disjoint_sameParity G (hs e.val e.property)
      (hs f.val f.property) (fun heq => hef (Subtype.ext heq))
      (hp e.val e.property f.val f.property))
    (fun e π => Real.exp (u * ((if boundaryAscent G e.val π then 1 else 0) -
      probability (uniformPermutation N) (boundaryAscent G e.val))))
    (by
      intro e π τ horder
      rw [propext (boundaryAscent_congr_relativeOrder G e.val π τ horder)])
  let F := fun (e : Fin (N-1)) (π : Permutation N) =>
    Real.exp (u * ((if boundaryAscent G e π then 1 else 0) -
      probability (uniformPermutation N) (boundaryAscent G e)))
  have hl (π : Permutation N) : (∏ e : s, F e.val π) = ∏ e ∈ s, F e π :=
    Finset.prod_coe_sort s (fun e => F e π)
  have hr : (∏ e : s, expect (uniformPermutation N) (F e.val)) =
      ∏ e ∈ s, expect (uniformPermutation N) (F e) :=
    Finset.prod_coe_sort s (fun e => expect (uniformPermutation N) (F e))
  change expect (uniformPermutation N) (fun π => ∏ e : s, F e.val π) =
    ∏ e : s, expect (uniformPermutation N) (F e.val) at h
  simp_rw [hl, hr] at h
  exact h

/-- Concrete component-sorting concentration with the frozen sharp exponent. -/
theorem componentConcentration : Targets.ComponentConcentration := by
  intro N G H M t hM hHM ht
  let B := retainedBoundaries G H
  let s₀ := B.filter fun e => boundaryParity G e = 0
  let s₁ := B.filter fun e => boundaryParity G e ≠ 0
  have hsum (π : Permutation N) :
      (ascentCount H (componentSort G π) : ℝ) = ((G ∩ internalEdges H).card : ℝ) +
        (∑ e ∈ s₀, if boundaryAscent G e π then (1 : ℝ) else 0) +
        (∑ e ∈ s₁, if boundaryAscent G e π then (1 : ℝ) else 0) := by
    rw [add_assoc]
    have hpartition := Finset.sum_filter_add_sum_filter_not B
      (fun e => boundaryParity G e = 0)
      (fun e => if boundaryAscent G e π then (1 : ℝ) else 0)
    rw [hpartition]
    exact_mod_cast component_ascent_decomposition G H π
  have hcard : (s₀.card : ℝ) + s₁.card ≤ M := by
    have heq : s₀.card+s₁.card = B.card :=
      Finset.card_filter_add_card_filter_not (fun e => boundaryParity G e = 0)
    have hb := retainedBoundaries_card_le G H
    have hcast : (s₀.card : ℝ) + s₁.card ≤ H.card := by exact_mod_cast heq.le.trans hb
    exact hcast.trans hHM
  apply two_class_indicator_concentration (uniformPermutation N)
    (fun π => (ascentCount H (componentSort G π) : ℝ))
    ((G ∩ internalEdges H).card : ℝ) s₀ s₁ (boundaryAscent G) hsum
    ?_ ?_ hM hcard ht
  · apply boundary_class_factorization
    · intro e he
      exact ((mem_retainedBoundaries G H e).mp (Finset.mem_filter.mp he).1).2
    · intro e he f hf
      exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
  · apply boundary_class_factorization
    · intro e he
      exact ((mem_retainedBoundaries G H e).mp (Finset.mem_filter.mp he).1).2
    · intro e he f hf
      have he0 := (Finset.mem_filter.mp he).2
      have hf0 := (Finset.mem_filter.mp hf).2
      have he2 := Nat.mod_lt (componentIndex G (edgeLeft e)) (by decide : 0 < 2)
      have hf2 := Nat.mod_lt (componentIndex G (edgeLeft f)) (by decide : 0 < 2)
      dsimp [boundaryParity] at *
      omega

theorem componentConcentrationTwoSided : Targets.ComponentConcentrationTwoSided :=
  componentConcentrationTwoSided_of_concentration componentConcentration

theorem uniformScan : Targets.UniformScan := uniformScan_of_concentration componentConcentration

end RiffleLowerV2.Ascent
