import RiffleUpperV2.Anchor.SourceSampling

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

/-- The entire global equality class, including labels outside the anchor. -/
def equalityRows {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (a : Fin k) (c : ColumnAssignments cuts j) : Finset (Fin n) :=
  Finset.univ.filter (fun r => c.val r = a)

theorem equalityRows_card {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (a : Fin k) (c : ColumnAssignments cuts j) : (equalityRows a c).card = cuts.count j a :=
  c.property a

/-- Revealing the equality class is equivalent to fixing all its values, since
the histogram forbids any additional occurrences of the equal digit. -/
theorem columnFiber_equalityRows_iff {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (a : Fin k) (c₀ c : ColumnAssignments cuts j) :
    columnFiber (equalityRows a c₀) c₀ c ↔ equalityRows a c = equalityRows a c₀ := by
  constructor
  · intro hc
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      have he : c₀.val r = a := (Finset.mem_filter.mp hr).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, (hc r hr).trans he⟩
    · rw [equalityRows_card, equalityRows_card]
  · intro he r hr
    have h₀ : c₀.val r = a := (Finset.mem_filter.mp hr).2
    have h : r ∈ equalityRows a c := he.symm ▸ hr
    exact (Finset.mem_filter.mp h).2.trans h₀.symm

/-- This is the exact fine fiber in the source's i_minus=i_plus case. -/
def equalRevealFiber {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d) (a : Fin k)
    (ω₀ ω : Sample cuts) : Prop :=
  (∀ t : Fin d, t ≠ j → ω t = ω₀ t) ∧ equalityRows a (ω j) = equalityRows a (ω₀ j)

theorem equalRevealFiber_iff {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d) (a : Fin k)
    (ω₀ ω : Sample cuts) :
    equalRevealFiber j a ω₀ ω ↔ partialRevealFiber j (equalityRows a (ω₀ j)) ω₀ ω := by
  exact and_congr_right (fun _ => (columnFiber_equalityRows_iff a (ω₀ j) (ω j)).symm)

theorem equalResidualMarked {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (a : Fin k) (c₀ : ColumnAssignments cuts j) :
    residualMarked (equalityRows a c₀) (Finset.univ.filter (· < a)) c₀ =
      Hypergeometric.allowedCount cuts j (Finset.univ.filter (· < a)) := by
  have he : (equalityRows a c₀).filter
      (fun r => c₀.val r ∈ Finset.univ.filter (· < a)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hr', lt_self_iff_false, not_false_eq_true]
  simp only [residualMarked, he, Finset.card_empty, Nat.sub_zero]

/-- Source eq:ub-anchor-hyp-case-equal, on the actual fixed-count matrix law.
The explicit population is n minus the global equal-digit count. -/
theorem equalRevealConditionalExpect {k n d : ℕ} (cuts : Cuts k n d)
    (j : Fin d) (a : Fin k) (B : Finset (Fin n)) (ω₀ : Sample cuts)
    (hB : B ⊆ Finset.univ \ equalityRows a (ω₀ j)) (f : ℕ → ℝ) :
    RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (B ∩ residualAllowed (equalityRows a (ω₀ j))
        (Finset.univ.filter (· < a)) (ω j)).card) (equalRevealFiber j a ω₀) =
    expect (sourceSamplingParams (equalityRows a (ω₀ j)) B
      (Finset.univ.filter (· < a)) (ω₀ j) hB).law.toPMF (fun q => f q.val) := by
  have he : equalRevealFiber j a ω₀ = partialRevealFiber j (equalityRows a (ω₀ j)) ω₀ := by
    funext ω
    exact propext (equalRevealFiber_iff j a ω₀ ω)
  rw [he]
  exact partialRevealSourceExpect cuts j _ B _ ω₀ hB f

/-- The source population/marked/sample values in the equal case are exact. -/
theorem equalRevealParameters {k n d : ℕ} (cuts : Cuts k n d)
    (j : Fin d) (a : Fin k) (B : Finset (Fin n)) (ω₀ : Sample cuts)
    (hB : B ⊆ Finset.univ \ equalityRows a (ω₀ j)) :
    let P := sourceSamplingParams (equalityRows a (ω₀ j)) B
      (Finset.univ.filter (· < a)) (ω₀ j) hB
    P.population = n - cuts.count j a ∧
    P.marked = Hypergeometric.allowedCount cuts j (Finset.univ.filter (· < a)) ∧
    P.draws = B.card := by
  dsimp only
  refine ⟨?_, equalResidualMarked a (ω₀ j), rfl⟩
  rw [sourceSamplingParams_population, equalityRows_card]

end RiffleUpperV2.Anchor
