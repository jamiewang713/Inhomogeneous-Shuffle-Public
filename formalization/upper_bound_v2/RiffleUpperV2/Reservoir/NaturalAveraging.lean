import RiffleUpperV2.Reservoir.GoodView
import RiffleUpperV2.Shared.SupportedAveraging

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem conditionalProbability_congr_on {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E F H : Ω → Prop) (h : ∀ ω, H ω → (E ω ↔ F ω)) :
    conditionalProbability P E H=conditionalProbability P F H := by
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  congr 1
  apply congrArg (probability P)
  funext ω
  apply propext
  exact ⟨fun he => ⟨(h ω he.2).mp he.1,he.2⟩,fun hf => ⟨(h ω hf.2).mpr hf.1,hf.2⟩⟩

/-- Supported disintegration preserves the exact conditional chance that
all marked labels belong to the chosen pile. This is the factor needed
when summing ordered marked tuples. -/
theorem natural_marked_good_upper_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ : ℝ, ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .forward (j.val+1) ω →
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      ∀ m : ℕ, (m=1 ∨ m=2) → ∀ f : Fin m ↪ Fin n, ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → pileWords cuts p ω j<w) →
      conditionalProbability (fixedCountPMF cuts)
        (fun z => markedTailEvent p f v z ∧ goodMarkedView cuts D g ξ p (Finset.univ.map f) z)
        (historyFiber cuts p .forward (j.val+1) ω) ≤
        ((2^m*(tailMass cuts E v)^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))) /
          ((reserveMass k D g)^m/2)) *
        conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f)
          (historyFiber cuts p .forward (j.val+1) ω) := by
  obtain ⟨N0,hN01,hN0⟩ := markedRefinement_prefix_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ p ω j hpos hdir m hm f E v hfuture
  let M := Finset.univ.map f
  let Z := markedRefinement cuts p (j.val+1) M
  let U := naturalHistory cuts p .forward (j.val+1)
  let H := historyFiber cuts p .forward (j.val+1) ω
  let S : Sample cuts → Prop := fun z => H z ∧ goodMarkedView cuts D g ξ p M z
  let b : ℝ := (2^m*(tailMass cuts E v)^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))) /
    ((reserveMass k D g)^m/2)
  let B := fun z : (Fin (pileSize cuts p) → Option (Word k (L+1))) ×
      (Finset (Fin n) × (Fin n → Option (Word k (L+1)))) => ∀ i, f i∈z.2.1
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
    (markedTailEvent p f v) S B hS (fun z hz => (hB z).mpr hz.1) b
    (by dsimp [b]; unfold tailMass reserveMass; positivity)
    (fun z _ hs hb => hN0 n hn L hL cuts hn0 hgood ξ p ω j hdir m hm f E v hfuture z hs.1
      ((hB z).mp hb) hs.2) (U ω) hpos
  have hleft : conditionalProbability (fixedCountPMF cuts)
      (fun z => markedTailEvent p f v z ∧ goodMarkedView cuts D g ξ p M z) H =
      conditionalProbability (fixedCountPMF cuts) (fun z => markedTailEvent p f v z ∧ S z) H := by
    apply conditionalProbability_congr_on
    intro z hz
    dsimp [S]
    tauto
  have hright : conditionalProbability (fixedCountPMF cuts) (fun z => B (Z z)) H =
      conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H := by
    apply conditionalProbability_congr_on
    intro z _
    exact hB z
  change conditionalProbability (fixedCountPMF cuts) (fun z => markedTailEvent p f v z ∧ S z) H ≤
    b*conditionalProbability (fixedCountPMF cuts) (fun z => B (Z z)) H at hh
  rw [hright,← hleft] at hh
  exact hh

/-- Removing the good-view restriction costs the history's single H-error,
independently of the number of possible suffix words. -/
theorem natural_marked_probability_good_bad {k n L m E : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ ε : ℝ) (p : Fin k) (f : Fin m ↪ Fin n)
    (ω : Sample cuts) (i : ℕ) (v : Word k (min E L))
    (hgood : historyGood cuts D g ξ ε p .forward i ω) :
    conditionalProbability (fixedCountPMF cuts) (markedTailEvent p f v)
      (historyFiber cuts p .forward i ω) ≤
    conditionalProbability (fixedCountPMF cuts)
      (fun z => markedTailEvent p f v z ∧ goodMarkedView cuts D g ξ p (Finset.univ.map f) z)
      (historyFiber cuts p .forward i ω)+ε := by
  exact (conditionalProbability_good_bad (fixedCountPMF cuts) _
    (goodMarkedView cuts D g ξ p (Finset.univ.map f)) (concentrationEvent cuts D g ξ)
    (historyFiber cuts p .forward i ω)
    (fun z _ hz => goodMarkedView_of_H cuts D g ξ p (Finset.univ.map f) z hz)).trans
    (add_le_add le_rfl hgood)

end RiffleUpperV2.Reservoir
