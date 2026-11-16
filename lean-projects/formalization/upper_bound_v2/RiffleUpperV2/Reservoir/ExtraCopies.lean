import RiffleUpperV2.Reservoir.CurrentMarked

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem sum_markedCurrent_indicators {k n L : ℕ} (cuts : Cuts k n (L+1))
    (s : Word k (L+1)) (t : ℕ) (ω : Sample cuts) :
    (∑ f : Fin 1 ↪ Fin n, if markedCurrentEvent f s t ω then (1:ℝ) else 0) =
      ((Finset.univ.filter fun r : Fin n => rowWord ω r=s ∧ t≤wordCount ω s-1).card:ℝ) := by
  have h := sum_marked_indicators (m := 1) (fun r : Fin n => rowWord ω r=s ∧ t≤wordCount ω s-1)
  simp only [RiffleLowerV2.falling,Nat.descFactorial_one] at h
  calc
    _ = ∑ f : Fin 1 ↪ Fin n, if ∀ i, rowWord ω (f i)=s ∧ t≤wordCount ω s-1 then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      have he : markedCurrentEvent f s t ω ↔ ∀ i, rowWord ω (f i)=s ∧ t≤wordCount ω s-1 := by
        constructor
        · exact fun h i => ⟨h.1 i,h.2⟩
        · exact fun h => ⟨fun i => (h i).1,(h 0).2⟩
      by_cases hh : markedCurrentEvent f s t ω
      · have hh' := he.mp hh
        simp only [if_pos hh,if_pos hh']
      · have hh' : ¬∀ i, rowWord ω (f i)=s ∧ t≤wordCount ω s-1 := fun h => hh (he.mpr h)
        simp [hh,hh']
    _ = _ := h

theorem conditionalExpect_mono_on {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (F G : Ω → ℝ) (H : Ω → Prop) (h : ∀ ω, H ω → F ω≤G ω) :
    conditionalExpect P F H≤conditionalExpect P G H := by
  unfold conditionalExpect RiffleLowerV2.conditionalExpect
  apply div_le_div_of_nonneg_right _ (RiffleLowerV2.Thinning.probability_nonneg P H)
  apply RiffleLowerV2.Thinning.expect_mono
  intro ω
  by_cases hh : H ω <;> simp only [hh,if_true,if_false]
  · exact h ω hh
  · exact le_rfl

theorem extraCurrentCopies_sum_bound {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (s : Word k (L+1)) (t : ℕ) (H : Sample cuts → Prop)
    (hH : 0<probability (fixedCountPMF cuts) H) (b ε : ℝ)
    (hb : ∀ f : Fin 1 ↪ Fin n,
      conditionalProbability (fixedCountPMF cuts) (markedCurrentEvent f s t) H≤
        b*conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H+ε) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => (wordCount ω s-t:ℕ)) H≤b*pileSize cuts p+n*ε := by
  have hsum := Finset.sum_le_sum (fun f (_ : f∈Finset.univ) => hb f)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_markedPile_conditionalProbability cuts p H hH,
    Finset.sum_const,Finset.card_univ,Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_fin,
    nsmul_eq_mul] at hsum
  simp only [RiffleLowerV2.falling,Nat.descFactorial_one] at hsum
  have hc : conditionalExpect (fixedCountPMF cuts)
      (fun ω => ((Finset.univ.filter fun r : Fin n => rowWord ω r=s ∧ t≤wordCount ω s-1).card:ℝ)) H =
      ∑ f : Fin 1 ↪ Fin n, conditionalProbability (fixedCountPMF cuts) (markedCurrentEvent f s t) H := by
    rw [← conditionalExpect_sum_marked]
    congr 1
    funext ω
    exact (sum_markedCurrent_indicators cuts s t ω).symm
  apply le_trans _ (hc.trans_le hsum)
  apply conditionalExpect_mono_on
  intro ω _
  exact_mod_cast removableCopies cuts ω s t

/-- Forced terminal copies are excluded from the excess. The remaining
copies obey the same uniform conditional prefix scale and one H-error. -/
theorem extraCurrentCopies (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1/2) :
    ∃ C1 : ℝ, 0<C1 ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ ε : ℝ, 0≤ε → ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .forward (j.val+1) ω →
      historyGood cuts D g ξ ε p .forward (j.val+1) ω →
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      conditionalExpect (fixedCountPMF cuts)
        (fun z => (wordCount z (pileWords cuts p ω j)-
          observedCount (pileWords cuts p ω) (j.val+1) (pileWords cuts p ω j):ℕ))
        (historyFiber cuts p .forward (j.val+1) ω) ≤
        C1*n*(RiffleLowerV2.wordMass cuts (pileWords cuts p ω j))^(1-Real.log (1/g)/Real.log (1/τ)) + n*ε := by
  obtain ⟨N0,hN01,hN0⟩ := markedRefinement_current_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT (by linarith)
  let C1 : ℝ := 2/(reserveMass k D g/2)
  have hC1 : 0<C1 := div_pos (by norm_num) (div_pos (reserveMass_pos hk hg) (by norm_num))
  refine ⟨C1,hC1,N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir
  let s := pileWords cuts p ω j
  let t := observedCount (pileWords cuts p ω) (j.val+1) s
  let H := historyFiber cuts p .forward (j.val+1) ω
  let b : ℝ := (2*(tailMass cuts L (tailPrefix L s))^(1-Real.log (1/g)/Real.log (1/τ)))/(reserveMass k D g/2)
  have hs : s.get 0=p := pileWords_first cuts p ω j
  have hb : 0≤b := by dsimp [b]; unfold tailMass reserveMass; positivity
  have hmarked : ∀ f : Fin 1 ↪ Fin n,
      conditionalProbability (fixedCountPMF cuts) (markedCurrentEvent f s t) H≤
        b*conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H+ε := by
    intro f
    have hgoodbound := supportedMarked_good_le cuts D g ξ p ω (j.val+1) f hpos (markedCurrentEvent f s t) b hb
      (fun z hz i => by rw [hz.1 i]; exact hs)
      (fun z hz hb hG => hN0 n hn L hL cuts hn0 hgood ξ p ω j hdir f z hz hb hG)
    have hbad := conditionalProbability_good_bad (fixedCountPMF cuts) (markedCurrentEvent f s t)
      (goodMarkedView cuts D g ξ p (Finset.univ.map f)) (concentrationEvent cuts D g ξ) H
      (fun z _ hz => goodMarkedView_of_H cuts D g ξ p (Finset.univ.map f) z hz)
    exact hbad.trans (add_le_add hgoodbound hhistory)
  have hsum := extraCurrentCopies_sum_bound cuts p s t H hpos b ε hmarked
  apply hsum.trans
  have hnorm := initialPile_normalization (m := 1) hn0
    (show pileSize cuts p≤n by have := pileOffset_add_size_le cuts p; omega)
    (q := tailMass cuts L (tailPrefix L s)) (by unfold tailMass; positivity)
    (rareExponent_nonneg hg hg1 hτ (hτg.trans hg1)) (by linarith : Real.log (1/g)/Real.log (1/τ)≤1)
  rw [pileTailMass_eq_prefixMass,← hs,tailBinPrefix_full] at hnorm
  rw [hs] at hnorm
  simp only [RiffleLowerV2.falling,Nat.descFactorial_one,pow_one,Nat.cast_one,one_mul] at hnorm
  have hh := mul_le_mul_of_nonneg_left hnorm hC1.le
  apply add_le_add _ le_rfl
  convert hh using 1 <;> (try dsimp only [b,C1,s,RiffleLowerV2.wordMass]) <;> ring

end RiffleUpperV2.Reservoir
