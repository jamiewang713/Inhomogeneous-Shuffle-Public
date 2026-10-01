import RiffleLowerV2.Ascent.Components.Charging
import RiffleLowerV2.Ascent.FiniteProbability
import RiffleLowerV2.Ascent.RelativeOrder.Boundary

/-! Exact clipped component expectation. All internal graph edges are retained. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Ascent

variable {N : ℕ}

theorem binomial_boundary_deficit_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : ℝ)/2 - 1/((a+b).choose a : ℝ) ≤ ((a-1 : ℕ)+(b-1 : ℕ) : ℝ)/6 := by
  by_cases hlarge : 5 ≤ a+b
  · have hweight : 3 ≤ (a-1)+(b-1) := by omega
    have hweight' : (3 : ℝ) ≤ ((a-1 : ℕ)+(b-1 : ℕ) : ℝ) := by exact_mod_cast hweight
    have hp : 0 ≤ 1/((a+b).choose a : ℝ) := by positivity
    linarith
  · have ha' : a ≤ 3 := by omega
    have hb' : b ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> norm_num [Nat.choose] at *

theorem component_expectation_eq (G : PathEdges N) (H : Finset (Fin N)) :
    expect (uniformPermutation N) (fun π => (ascentCount H (componentSort G π) : ℝ)) =
      ((G ∩ internalEdges H).card : ℝ) +
        ∑ e ∈ retainedBoundaries G H, probability (uniformPermutation N) (boundaryAscent G e) := by
  have hfun : (fun π => (ascentCount H (componentSort G π) : ℝ)) =
      (fun π => ((G ∩ internalEdges H).card : ℝ) +
        ∑ e ∈ retainedBoundaries G H, if boundaryAscent G e π then (1 : ℝ) else 0) := by
    funext π
    rw [component_ascent_decomposition]
    simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hfun, expect_add, expect_const, expect_sum]
  simp only [expect_indicator]

theorem badBoundaries_subset (G : PathEdges N) (H : Finset (Fin N)) :
    badBoundaries G H ⊆ retainedBoundaries G H := by
  intro e he
  rcases Finset.mem_union.mp he with hl | hr
  · exact (Finset.mem_filter.mp hl).1
  · exact (Finset.mem_filter.mp hr).1

theorem good_bad_disjoint (G : PathEdges N) (H : Finset (Fin N)) :
    Disjoint (goodBoundaries G H) (badBoundaries G H) := by
  apply Finset.disjoint_left.mpr
  intro e he hb
  exact (Finset.mem_sdiff.mp he).2 hb

theorem good_bad_union (G : PathEdges N) (H : Finset (Fin N)) :
    goodBoundaries G H ∪ badBoundaries G H = retainedBoundaries G H := by
  exact Finset.sdiff_union_of_subset (badBoundaries_subset G H)

theorem retained_edges_card_partition (G : PathEdges N) (H : Finset (Fin N)) :
    (internalEdges H).card = (G ∩ internalEdges H).card +
      (goodBoundaries G H).card + (badBoundaries G H).card := by
  have hpart : (G ∩ internalEdges H) ∪ retainedBoundaries G H = internalEdges H := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter, mem_retainedBoundaries]
    tauto
  have hd : Disjoint (G ∩ internalEdges H) (retainedBoundaries G H) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact ((mem_retainedBoundaries G H e).mp hf).2 (Finset.mem_inter.mp he).1
  have hc := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hd] at hc
  have hg := congrArg Finset.card (good_bad_union G H)
  rw [Finset.card_union_of_disjoint (good_bad_disjoint G H)] at hg
  omega

theorem component_expectation_lower_of_boundary_probability
    (G : PathEdges N) (H : Finset (Fin N))
    (hprob : ∀ e : Fin (N-1), e ∉ G →
      probability (uniformPermutation N) (boundaryAscent G e) =
        1 / (((leftComponent G e).card + (rightComponent G e).card).choose
          (leftComponent G e).card : ℝ)) :
    expect (uniformPermutation N) (fun π => (ascentCount H (componentSort G π) : ℝ)) ≥
      ((internalEdges H).card : ℝ)/2 + ((G ∩ internalEdges H).card : ℝ)/6 - (boundary H).card := by
  let p := fun e => probability (uniformPermutation N) (boundaryAscent G e)
  let w := fun e : Fin (N-1) => ((leftComponent G e).card - 1) + ((rightComponent G e).card - 1)
  have hp (e : Fin (N-1)) : 0 ≤ p e := probability_nonneg _ _
  have hlocal : ∀ e ∈ goodBoundaries G H, (1 : ℝ)/2 - (w e : ℝ)/6 ≤ p e := by
    intro e he
    have hn := ((mem_retainedBoundaries G H e).mp ((mem_goodBoundaries G H e).mp he).1).2
    have hl : 1 ≤ (leftComponent G e).card := by
      apply Finset.card_pos.mpr
      exact ⟨edgeLeft e, by simp [leftComponent]⟩
    have hr : 1 ≤ (rightComponent G e).card := by
      apply Finset.card_pos.mpr
      exact ⟨edgeRight e, by simp [rightComponent]⟩
    have hd := binomial_boundary_deficit_le _ _ hl hr
    dsimp [p]
    rw [hprob e hn]
    dsimp [w]
    push_cast
    linarith
  have hsum := Finset.sum_le_sum hlocal
  have hw : (∑ e ∈ goodBoundaries G H, (w e : ℝ)) ≤ 2 * ((G ∩ internalEdges H).card : ℝ) := by
    exact_mod_cast good_boundary_double_charge G H
  have hsum' : ((goodBoundaries G H).card : ℝ)/2 -
      (∑ e ∈ goodBoundaries G H, (w e : ℝ))/6 ≤ ∑ e ∈ goodBoundaries G H, p e := by
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
      nsmul_eq_mul, mul_one_div, mul_one] using hsum
  have hgood : ((goodBoundaries G H).card : ℝ)/2 - ((G ∩ internalEdges H).card : ℝ)/3 ≤
      ∑ e ∈ goodBoundaries G H, p e := by linarith
  have hbad : 0 ≤ ∑ e ∈ badBoundaries G H, p e := Finset.sum_nonneg (fun e _ => hp e)
  have hpart : ((internalEdges H).card : ℝ) = ((G ∩ internalEdges H).card : ℝ) +
      ((goodBoundaries G H).card : ℝ) + ((badBoundaries G H).card : ℝ) := by
    exact_mod_cast retained_edges_card_partition G H
  have hbadcard : ((badBoundaries G H).card : ℝ) ≤ 2 * ((boundary H).card : ℝ) := by
    exact_mod_cast badBoundaries_card_le G H
  rw [component_expectation_eq, ← good_bad_union G H,
    Finset.sum_union (good_bad_disjoint G H)]
  change _ ≤ ((G ∩ internalEdges H).card : ℝ) +
    ((∑ e ∈ goodBoundaries G H, p e) + ∑ e ∈ badBoundaries G H, p e)
  linarith

/-- `lem:component-ascent-expectation`, on the frozen component sort and integer boundary. -/
theorem componentExpectation : Targets.ComponentExpectation := by
  intro N G H
  apply component_expectation_lower_of_boundary_probability G H
  intro e he
  exact boundaryAscentProbability N (leftComponent G e) (rightComponent G e)
    (left_right_disjoint G e he)

end RiffleLowerV2.Ascent
