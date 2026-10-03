import RiffleUpperV2.Exploration.Objects

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exploration

theorem chosenReserves_spec {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (h : chosenReserves cuts D g = some v) :
    v.1 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      reserveMass k D g ≤ tailMass cuts D v.1 ∧
      reserveMass k D g ≤ tailMass cuts D v.2.1 ∧
      reserveMass k D g ≤ tailMass cuts D v.2.2 := by
  unfold chosenReserves at h
  split_ifs at h with hc
  · have hv : (reserveCandidates cuts D g).min' hc = v := Option.some.inj h
    have hm := (reserveCandidates cuts D g).min'_mem hc
    rw [hv] at hm
    exact (Finset.mem_filter.mp hm).2

theorem chosenReserves_exists_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ) :
    (∃ v, chosenReserves cuts D g = some v) ↔ (reserveCandidates cuts D g).Nonempty := by
  simp only [chosenReserves]
  split_ifs with h <;> simp [h]

theorem reserveMass_pos {k D : ℕ} (hk : 0 < k) {g : ℝ} (hg : 0 < g) :
    0 < reserveMass k D g := by
  unfold reserveMass
  positivity

/-- Every word has a direction, and the middle cylinder belongs to both. -/
theorem direction_cover_word {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (hc : (reserveCandidates cuts D g).Nonempty) (w : Word k (L+1)) :
    hasDirection cuts D g .forward w ∨ hasDirection cuts D g .backward w := by
  obtain ⟨v, hv⟩ := (chosenReserves_exists_iff cuts D g).2 hc
  simp only [hasDirection, hv]
  exact le_total _ _

theorem direction_overlap_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g = some v) (w : Word k (L+1)) :
    hasDirection cuts D g .forward w ∧ hasDirection cuts D g .backward w ↔
      tailPrefix D w = v.2.1 := by
  simp only [hasDirection, hv]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- Scalar guard separation. This does not assume any independence between matrices. -/
theorem guard_interlace {b₁ t₂ l u δ : ℝ} (hδ : 0 < δ) (hgap : δ ≤ u-l)
    (hb : |b₁-l| ≤ δ/4) (ht : |t₂-u| ≤ δ/4) : b₁ < t₂ := by
  have hb' := (abs_le.mp hb).2
  have ht' := (abs_le.mp ht).1
  linarith

/-- The two impossible opposite-side rank inequalities in the manuscript. -/
theorem no_crossed_edge {before through edge : ℕ} (hsep : before ≤ through)
    (hleft : edge+1 ≤ before) (hright : through+1 ≤ edge) : False := by omega

end RiffleUpperV2.Exploration
