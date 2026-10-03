import RiffleUpperV2.Reservoir.CollisionNormalization

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

theorem markedWordEvent_fullTail_iff {k n L m : ℕ} (cuts : Cuts k n (L+1))
    (f : Fin m ↪ Fin n) (p : Fin k) (w : Word k (L+1)) (hp : w.get 0=p) (z : Sample cuts) :
    markedWordEvent f w z ↔ markedTailEvent p f (tailPrefix L w) z := by
  constructor
  · intro h
    exact ⟨fun i => by rw [h i]; exact hp, fun i => by rw [h i]⟩
  · intro h i
    exact word_eq_of_head_tail_full _ _ ((h.1 i).trans hp.symm) (h.2 i)

/-- Full-word good probabilities are summed before the single exceptional
probability is charged to a marked pair. -/
theorem natural_markedCollision_upper_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ ε : ℝ, ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .forward (j.val+1) ω →
      historyGood cuts D g ξ ε p .forward (j.val+1) ω →
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      ∀ f : Fin 2 ↪ Fin n, ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → pileWords cuts p ω j<w) →
      conditionalProbability (fixedCountPMF cuts) (markedCollisionEvent f (tailBinPrefix E p v))
        (historyFiber cuts p .forward (j.val+1) ω) ≤
      (4/((reserveMass k D g)^2/2))*tailExtensionPowerMass cuts (tailBinPrefix E p v)
        (2*(1-Real.log (1/g)/Real.log (1/τ)))*
        conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f)
          (historyFiber cuts p .forward (j.val+1) ω)+ε := by
  obtain ⟨N0,hN01,hN0⟩ := natural_marked_good_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε p ω j hpos hhistory hdir f E v hfuture
  let H := historyFiber cuts p .forward (j.val+1) ω
  let G := goodMarkedView cuts D g ξ p (Finset.univ.map f)
  let x := tailBinPrefix E p v
  have hgoodbound : conditionalProbability (fixedCountPMF cuts) (fun z => markedCollisionEvent f x z ∧ G z) H ≤
      (4/((reserveMass k D g)^2/2))*tailExtensionPowerMass cuts x (2*(1-Real.log (1/g)/Real.log (1/τ)))*
        conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H := by
    rw [conditionalCollision_good_partition]
    unfold tailExtensionPowerMass
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : w.toList.take x.1.val=x.2.toList
    · simp only [if_pos hw]
      have hp : w.get 0=p := ((tailBinPrefix_word E p v w).mp hw).1
      have ht : tailPrefix E w=v := ((tailBinPrefix_word E p v w).mp hw).2
      have hb := hN0 n hn L hL cuts hn0 hgood ξ p ω j hpos hdir 2 (Or.inr rfl) f L (tailPrefix L w)
        (fun u hu hut => by
          have he : u=w := word_eq_of_head_tail_full u w (hu.trans hp.symm) hut
          rw [he]
          exact hfuture w hp ht)
      have hevent : (fun z : Sample cuts => markedWordEvent f w z ∧ G z)=
          (fun z => markedTailEvent p f (tailPrefix L w) z ∧ G z) := by
        funext z
        exact propext (and_congr_left (fun _ => markedWordEvent_fullTail_iff cuts f p w hp z))
      rw [hevent]
      dsimp only [G,H]
      convert hb using 1 <;> norm_num only [Nat.cast_ofNat] <;> first | rfl | ring
    · simp only [hw,if_false,mul_zero,zero_mul,le_refl]
  have hbad := conditionalProbability_good_bad (fixedCountPMF cuts) (markedCollisionEvent f x) G
    (concentrationEvent cuts D g ξ) H (fun z _ hz => goodMarkedView_of_H cuts D g ξ p (Finset.univ.map f) z hz)
  exact hbad.trans (add_le_add hgoodbound hhistory)

end RiffleUpperV2.Reservoir
