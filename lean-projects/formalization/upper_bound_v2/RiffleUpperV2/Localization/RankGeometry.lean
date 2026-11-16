import RiffleUpperV2.Localization.CylinderAdapters

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Localization
open Anchor

theorem endpoint_offset {k n d : ℕ} {cuts : Cuts k n d} (c b : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    lowerEndpoint (c+b) R x ω = lowerEndpoint c R x ω + b ∧
    upperEndpoint (c+b) R x ω = upperEndpoint c R x ω + b := by
  simp only [lowerEndpoint, upperEndpoint]
  constructor <;> omega

private theorem filter_lt_add_eq {α : Type*} {k : ℕ}
    (R : Finset α) (f : α → List (Fin k)) (b : List (Fin k)) :
    (R.filter (fun r => f r < b)).card + (R.filter (fun r => f r = b)).card =
      (R.filter (fun r => f r ≤ b)).card := by
  have hdis : Disjoint (R.filter (fun r => f r < b)) (R.filter (fun r => f r = b)) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    exact (ne_of_lt (Finset.mem_filter.mp hr).2) (Finset.mem_filter.mp hs).2
  rw [← Finset.card_union_of_disjoint hdis]
  congr 1
  ext r
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hr,hlt⟩ | ⟨hr,heq⟩)
    · exact ⟨hr,hlt.le⟩
    · exact ⟨hr,heq.le⟩
  · rintro ⟨hr,hle⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl ⟨hr,h⟩
    · exact Or.inr ⟨hr,h⟩

theorem upperEndpoint_eq_le_count {k n d : ℕ} {cuts : Cuts k n d} (c : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    upperEndpoint c R x ω = c +
      ((R.filter (fun r => (rowWord ω r).toList.take x.1.val ≤ x.2.toList)).card : ℤ) := by
  unfold upperEndpoint lowerEndpoint prefixRows
  rw [add_assoc, ← Nat.cast_add]
  exact congrArg (fun q : ℕ => c + (q : ℤ)) (filter_lt_add_eq R
    (fun r => (rowWord ω r).toList.take x.1.val) x.2.toList)

theorem same_depth_endpoints_ordered {k n d : ℕ} {cuts : Cuts k n d} (c : ℤ)
    (R : Finset (Fin n)) {x y : Prefix k d} (hlen : x.1.val = y.1.val)
    (hxy : x.2.toList < y.2.toList) (ω : Sample cuts) :
    upperEndpoint c R x ω ≤ lowerEndpoint c R y ω := by
  rw [upperEndpoint_eq_le_count]
  unfold lowerEndpoint
  apply add_le_add_right
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro r hr
  obtain ⟨hr,hrow⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hr, by simpa only [hlen] using hrow.trans_lt hxy⟩

/-- The deterministic mean length is the anchored expected cylinder size. -/
theorem expected_endpoint_length {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (c : ℤ) (R : Finset (Fin n)) (x : Prefix k d) :
    expect (fixedCountPMF cuts) (fun ω => (upperEndpoint c R x ω : ℝ)) -
      expect (fixedCountPMF cuts) (fun ω => (lowerEndpoint c R x ω : ℝ)) =
        anchoredMean cuts R x := by
  have hfun : (fun ω : Sample cuts => (upperEndpoint c R x ω : ℝ)) =
      fun ω => (lowerEndpoint c R x ω : ℝ) + ((prefixRows R x ω).card : ℝ) := by
    funext ω
    simp [upperEndpoint]
  rw [hfun]
  change RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) _ - _ = _
  rw [RiffleLowerV2.Thinning.expect_add]
  have hm := prefixRows_expect cuts hn R x
  change RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) _ = _ at hm
  linarith

end RiffleUpperV2.Localization
