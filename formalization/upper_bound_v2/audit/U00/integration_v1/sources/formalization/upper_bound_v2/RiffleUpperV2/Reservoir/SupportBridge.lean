import RiffleUpperV2.Reservoir.NaturalAveraging

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile

theorem supportedMarked_good_le {k n L m : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ)
    (g ξ : ℝ) (p : Fin k) (ω : Sample cuts) (i : ℕ) (f : Fin m ↪ Fin n)
    (hpos : positiveHistory cuts p .forward i ω) (Event : Sample cuts → Prop) (b : ℝ) (hb : 0≤b)
    (hsupport : ∀ z, Event z → markedPileEvent p f z)
    (hpoint : ∀ z, historyFiber cuts p .forward i ω z → markedPileEvent p f z →
      goodMarkedView cuts D g ξ p (Finset.univ.map f) z →
      conditionalProbability (fixedCountPMF cuts) Event
        (fun w => markedRefinement cuts p i (Finset.univ.map f) w=markedRefinement cuts p i (Finset.univ.map f) z)≤b) :
    conditionalProbability (fixedCountPMF cuts)
      (fun z => Event z ∧ goodMarkedView cuts D g ξ p (Finset.univ.map f) z)
      (historyFiber cuts p .forward i ω) ≤
      b*conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) (historyFiber cuts p .forward i ω) := by
  let M := Finset.univ.map f
  let Z := markedRefinement cuts p i M
  let U := naturalHistory cuts p .forward i
  let H := historyFiber cuts p .forward i ω
  let S : Sample cuts → Prop := fun z => H z ∧ goodMarkedView cuts D g ξ p M z
  let B := fun z : (Fin (pileSize cuts p) → Option (Word k (L+1))) ×
      (Finset (Fin n) × (Fin n → Option (Word k (L+1)))) => ∀ j, f j∈z.2.1
  have hB (z : Sample cuts) : B (Z z) ↔ markedPileEvent p f z := by
    simp only [B,Z,markedRefinement,exposedPileView,pileLabels,Finset.mem_filter,Finset.mem_univ,true_and,markedPileEvent]
  have href : ∀ z z', Z z=Z z' → U z=U z' := fun _ _ h => congrArg Prod.fst h
  have hS : ∀ z z', Z z=Z z' → (S z ↔ S z') := by
    intro z z' hh
    have hu := href z z' hh
    have hv := congrArg Prod.snd hh
    change (U z=U ω ∧ goodMarkedView cuts D g ξ p M z) ↔
      (U z'=U ω ∧ goodMarkedView cuts D g ξ p M z')
    rw [hu]
    exact and_congr_right (fun _ => goodMarkedView_invariant cuts D g ξ p M z z' hv)
  have hh := conditionalSupportedGoodEvent_le (fixedCountPMF cuts) Z U href
    Event S B hS (fun z hz => (hB z).mpr (hsupport z hz)) b hb
    (fun z _ hs hb => hpoint z hs.1 ((hB z).mp hb) hs.2) (U ω) hpos
  have hleft : conditionalProbability (fixedCountPMF cuts)
      (fun z => Event z ∧ goodMarkedView cuts D g ξ p M z) H =
      conditionalProbability (fixedCountPMF cuts) (fun z => Event z ∧ S z) H := by
    apply conditionalProbability_congr_on
    intro z hz
    dsimp [S]
    tauto
  have hright : conditionalProbability (fixedCountPMF cuts) (fun z => B (Z z)) H =
      conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H := by
    apply conditionalProbability_congr_on
    intro z _
    exact hB z
  change conditionalProbability (fixedCountPMF cuts) (fun z => Event z ∧ S z) H ≤
    b*conditionalProbability (fixedCountPMF cuts) (fun z => B (Z z)) H at hh
  rw [hright,← hleft] at hh
  exact hh

end RiffleUpperV2.Reservoir
