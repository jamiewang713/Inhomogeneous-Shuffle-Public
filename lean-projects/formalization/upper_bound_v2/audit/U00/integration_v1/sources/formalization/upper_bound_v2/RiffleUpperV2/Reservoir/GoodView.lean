import RiffleUpperV2.Reservoir.MarkedRefinement

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile

theorem goodMarkedView_invariant {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (M : Finset (Fin n)) (ω z : Sample cuts)
    (h : exposedPileView p M ω=exposedPileView p M z) :
    goodMarkedView cuts D g ξ p M ω ↔ goodMarkedView cuts D g ξ p M z := by
  constructor
  · rintro ⟨w,hw,hH⟩
    exact ⟨w,hw.trans h,hH⟩
  · rintro ⟨w,hw,hH⟩
    exact ⟨w,hw.trans h.symm,hH⟩

theorem markedPileEvent_invariant {k n L m : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (f : Fin m ↪ Fin n) (M : Finset (Fin n)) (ω z : Sample cuts)
    (h : exposedPileView p M ω=exposedPileView p M z) :
    markedPileEvent p f ω ↔ markedPileEvent p f z := by
  have hp := congrArg Prod.fst h
  change pileLabels p ω=pileLabels p z at hp
  have hh (r : Fin n) : (rowWord ω r).get 0=p ↔ (rowWord z r).get 0=p := by
    have hm := Finset.ext_iff.mp hp r
    simpa only [pileLabels,Finset.mem_filter,Finset.mem_univ,true_and] using hm
  exact forall_congr' (fun i => hh (f i))

/-- Charge the complement of H once for a whole marked event. There is no
sum over possible terminal words inside the exceptional contribution. -/
theorem conditionalProbability_good_bad {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E S G H : Ω → Prop) (hS : ∀ ω, H ω → G ω → S ω) :
    conditionalProbability P E H ≤ conditionalProbability P (fun ω => E ω ∧ S ω) H +
      conditionalProbability P (fun ω => ¬G ω) H := by
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (RiffleLowerV2.Thinning.probability_nonneg P H)
  apply (RiffleLowerV2.Thinning.probability_mono P (fun ω h => ?_)).trans
    (RiffleLowerV2.Thinning.probability_union_le P _ _)
  by_cases hG : G ω
  · exact Or.inl ⟨⟨h.1,hS ω h.2 hG⟩,h.2⟩
  · exact Or.inr ⟨hG,h.2⟩

end RiffleUpperV2.Reservoir
