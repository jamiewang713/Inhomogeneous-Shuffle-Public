import RiffleUpperV2.Localization.RankGeometry
import RiffleUpperV2.Shared.Anchored

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Localization
open Anchor

theorem prefix_endpoint_inclusion {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) {v x : Prefix k d} (hvx : IsPrefix v x) (ω : Sample cuts) :
    lowerEndpoint c₀ R v ω ≤ lowerEndpoint c₀ R x ω ∧
      upperEndpoint c₀ R x ω ≤ upperEndpoint c₀ R v ω := by
  have hlen := prefix_length_le hvx
  have ht : x.2.toList.take v.1.val = v.2.toList := by
    simpa only [List.Vector.toList_length] using (List.prefix_iff_eq_take.mp hvx).symm
  have hrow (r : Fin n) : ((rowWord ω r).toList.take x.1.val).take v.1.val =
      (rowWord ω r).toList.take v.1.val := by
    rw [List.take_take,Nat.min_eq_left hlen]
  constructor
  · unfold lowerEndpoint
    apply add_le_add_right
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro r hr
    obtain ⟨hr,hlt⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨hr,?_⟩
    by_contra hnot
    have hle := RiffleShuffle.take_lex_monotone v.1.val (le_of_not_gt hnot)
    rw [ht,hrow] at hle
    exact not_le_of_gt hlt hle
  · rw [upperEndpoint_eq_le_count,upperEndpoint_eq_le_count]
    apply add_le_add_right
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro r hr
    obtain ⟨hr,hle⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨hr,?_⟩
    have h := RiffleShuffle.take_lex_monotone v.1.val hle
    rwa [ht,hrow] at h

theorem anchoredInterval_subset {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) {v x : Prefix k d} (hvx : IsPrefix v x) (ω : Sample cuts) :
    anchoredInterval c₀ R x ω ⊆ anchoredInterval c₀ R v ω := by
  intro m hm
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hm
  obtain ⟨hl,hu⟩ := prefix_endpoint_inclusion c₀ R hvx ω
  exact Finset.mem_Ico.mpr ⟨hl.trans hlo,hhi.trans_le hu⟩

def meanLower {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) : ℝ :=
  expect (fixedCountPMF cuts) (fun ω => (lowerEndpoint c₀ R x ω : ℝ))

def meanUpper {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) : ℝ :=
  expect (fixedCountPMF cuts) (fun ω => (upperEndpoint c₀ R x ω : ℝ))

theorem mean_intervals_ordered {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) {x y : Prefix k d} (hlen : x.1.val = y.1.val)
    (hxy : x.2.toList < y.2.toList) :
    meanUpper cuts c₀ R x ≤ meanLower cuts c₀ R y := by
  apply RiffleLowerV2.Thinning.expect_mono
  intro ω
  exact_mod_cast same_depth_endpoints_ordered c₀ R hlen hxy ω

end RiffleUpperV2.Localization
