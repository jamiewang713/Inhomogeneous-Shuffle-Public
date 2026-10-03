import RiffleUpperV2.Reservoir.BackwardRefinement
import RiffleUpperV2.Reservoir.TailCollisions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir.Backward
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
      positiveHistory cuts p .backward (j.val+1) ω →
      hasDirection cuts D g .backward (backwardWords cuts p ω j) →
      ∀ m : ℕ, (m=1 ∨ m=2) → ∀ f : Fin m ↪ Fin n, ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → w<backwardWords cuts p ω j) →
      conditionalProbability (fixedCountPMF cuts)
        (fun z => markedTailEvent p f v z ∧ goodMarkedView cuts D g ξ p (Finset.univ.map f) z)
        (historyFiber cuts p .backward (j.val+1) ω) ≤
        ((2^m*(tailMass cuts E v)^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))) /
          ((reserveMass k D g)^m/2)) *
        conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f)
          (historyFiber cuts p .backward (j.val+1) ω) := by
  obtain ⟨N0,hN01,hN0⟩ := backward_markedRefinement_prefix_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ p ω j hpos hdir m hm f E v hfuture
  let M := Finset.univ.map f
  let Z := backwardMarkedRefinement cuts p (j.val+1) M
  let U := naturalHistory cuts p .backward (j.val+1)
  let H := historyFiber cuts p .backward (j.val+1) ω
  let S : Sample cuts → Prop := fun z => H z ∧ goodMarkedView cuts D g ξ p M z
  let b : ℝ := (2^m*(tailMass cuts E v)^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))) /
    ((reserveMass k D g)^m/2)
  let B := fun z : (Fin (pileSize cuts p) → Option (Word k (L+1))) ×
      (Finset (Fin n) × (Fin n → Option (Word k (L+1)))) => ∀ i, f i∈z.2.1
  have hB (z : Sample cuts) : B (Z z) ↔ markedPileEvent p f z := by
    simp only [B,Z,backwardMarkedRefinement,exposedPileView,pileLabels,Finset.mem_filter,Finset.mem_univ,true_and,markedPileEvent]
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
    (hgood : historyGood cuts D g ξ ε p .backward i ω) :
    conditionalProbability (fixedCountPMF cuts) (markedTailEvent p f v)
      (historyFiber cuts p .backward i ω) ≤
    conditionalProbability (fixedCountPMF cuts)
      (fun z => markedTailEvent p f v z ∧ goodMarkedView cuts D g ξ p (Finset.univ.map f) z)
      (historyFiber cuts p .backward i ω)+ε := by
  exact (conditionalProbability_good_bad (fixedCountPMF cuts) _
    (goodMarkedView cuts D g ξ p (Finset.univ.map f)) (concentrationEvent cuts D g ξ)
    (historyFiber cuts p .backward i ω)
    (fun z _ hz => goodMarkedView_of_H cuts D g ξ p (Finset.univ.map f) z hz)).trans
    (add_le_add le_rfl hgood)



theorem supportedMarked_good_le {k n L m : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ)
    (g ξ : ℝ) (p : Fin k) (ω : Sample cuts) (i : ℕ) (f : Fin m ↪ Fin n)
    (hpos : positiveHistory cuts p .backward i ω) (Event : Sample cuts → Prop) (b : ℝ) (hb : 0≤b)
    (hsupport : ∀ z, Event z → markedPileEvent p f z)
    (hpoint : ∀ z, historyFiber cuts p .backward i ω z → markedPileEvent p f z →
      goodMarkedView cuts D g ξ p (Finset.univ.map f) z →
      conditionalProbability (fixedCountPMF cuts) Event
        (fun w => backwardMarkedRefinement cuts p i (Finset.univ.map f) w=backwardMarkedRefinement cuts p i (Finset.univ.map f) z)≤b) :
    conditionalProbability (fixedCountPMF cuts)
      (fun z => Event z ∧ goodMarkedView cuts D g ξ p (Finset.univ.map f) z)
      (historyFiber cuts p .backward i ω) ≤
      b*conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) (historyFiber cuts p .backward i ω) := by
  let M := Finset.univ.map f
  let Z := backwardMarkedRefinement cuts p i M
  let U := naturalHistory cuts p .backward i
  let H := historyFiber cuts p .backward i ω
  let S : Sample cuts → Prop := fun z => H z ∧ goodMarkedView cuts D g ξ p M z
  let B := fun z : (Fin (pileSize cuts p) → Option (Word k (L+1))) ×
      (Finset (Fin n) × (Fin n → Option (Word k (L+1)))) => ∀ j, f j∈z.2.1
  have hB (z : Sample cuts) : B (Z z) ↔ markedPileEvent p f z := by
    simp only [B,Z,backwardMarkedRefinement,exposedPileView,pileLabels,Finset.mem_filter,Finset.mem_univ,true_and,markedPileEvent]
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



theorem pileTailMass_eq_prefixMass {k n L E : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (v : Word k (min E L)) :
    ((pileSize cuts p:ℝ)/n)*tailMass cuts E v=RiffleUpperV2.prefixMass cuts (tailBinPrefix E p v) := by
  unfold RiffleUpperV2.prefixMass RiffleLowerV2.prefixMass tailBinPrefix
  rw [Fin.prod_univ_succ]
  simp only [List.Vector.get_cons_zero,List.Vector.get_cons_succ]
  rfl

/-- Actual natural-history factorial count estimate, with the bad event
charged once for each ordered marked tuple and the exact pile factor kept. -/
theorem natural_prefixFactorial_upper_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ ε : ℝ, 0≤ε → ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .backward (j.val+1) ω →
      historyGood cuts D g ξ ε p .backward (j.val+1) ω →
      hasDirection cuts D g .backward (backwardWords cuts p ω j) →
      ∀ m : ℕ, (m=1 ∨ m=2) → ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → w<backwardWords cuts p ω j) →
      conditionalExpect (fixedCountPMF cuts) (fun z => RiffleLowerV2.falling (pileTailCount p v z) m)
        (historyFiber cuts p .backward (j.val+1) ω) ≤
      (2^m/((reserveMass k D g)^m/2))*(n:ℝ)^m*
        (RiffleUpperV2.prefixMass cuts (tailBinPrefix E p v))^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))+
        (n:ℝ)^m*ε := by
  obtain ⟨N0,hN01,hN0⟩ := natural_marked_good_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir m hm E v hfuture
  let H := historyFiber cuts p .backward (j.val+1) ω
  let b : ℝ := (2^m*(tailMass cuts E v)^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))) /
    ((reserveMass k D g)^m/2)
  have hb : ∀ f : Fin m ↪ Fin n,
      conditionalProbability (fixedCountPMF cuts) (markedTailEvent p f v) H ≤
        b*conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H+ε := by
    intro f
    exact (natural_marked_probability_good_bad cuts D g ξ ε p f ω (j.val+1) v hhistory).trans
      (add_le_add (hN0 n hn L hL cuts hn0 hgood ξ p ω j hpos hdir m hm f E v hfuture) le_rfl)
  have hsum := Finset.sum_le_sum (fun f (_ : f∈Finset.univ) => hb f)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_markedPile_conditionalProbability cuts p H hpos,
    Finset.sum_const,Finset.card_univ,Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hcount : conditionalExpect (fixedCountPMF cuts)
      (fun z => RiffleLowerV2.falling (pileTailCount p v z) m) H =
      ∑ f : Fin m ↪ Fin n, conditionalProbability (fixedCountPMF cuts) (markedTailEvent p f v) H := by
    rw [← conditionalExpect_sum_marked]
    congr 1
    funext z
    exact (sum_markedTail_indicators cuts p v z).symm
  rw [hcount]
  apply hsum.trans
  have hnorm := initialPile_normalization (m := m) hn0
    (show pileSize cuts p≤n by have := pileOffset_add_size_le cuts p; omega)
    (q := tailMass cuts E v) (by unfold tailMass; positivity)
    (rareExponent_nonneg hg hg1 hτ (hτg.trans hg1)) hα.le
  rw [pileTailMass_eq_prefixMass] at hnorm
  have hcoef : 0≤(2:ℝ)^m/((reserveMass k D g)^m/2) := by unfold reserveMass; positivity
  have hmain := mul_le_mul_of_nonneg_left hnorm hcoef
  have hfall : (n.descFactorial m:ℝ)≤(n:ℝ)^m := by exact_mod_cast Nat.descFactorial_le_pow n m
  have herr := mul_le_mul_of_nonneg_right hfall hε
  convert add_le_add hmain herr using 1 <;> (try dsimp only [b]) <;> ring

/-- The source conditional cylinder-count estimate for every positive
backward natural history. Constants are fixed before the cut array. -/
theorem prefixCount (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1/2) :
    ∃ C1 : ℝ, 0<C1 ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ ε : ℝ, 0≤ε → ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .backward (j.val+1) ω →
      historyGood cuts D g ξ ε p .backward (j.val+1) ω →
      hasDirection cuts D g .backward (backwardWords cuts p ω j) →
      ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → w<backwardWords cuts p ω j) →
      conditionalExpect (fixedCountPMF cuts)
        (fun z => (RiffleUpperV2.prefixCount (tailBinPrefix E p v) z:ℝ))
        (historyFiber cuts p .backward (j.val+1) ω) ≤
        C1*n*(RiffleUpperV2.prefixMass cuts (tailBinPrefix E p v))^(1-Real.log (1/g)/Real.log (1/τ)) + n*ε := by
  obtain ⟨N0,hN01,hN0⟩ := natural_prefixFactorial_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT (by linarith)
  refine ⟨2/(reserveMass k D g/2),by exact div_pos (by norm_num) (div_pos (reserveMass_pos hk hg) (by norm_num)),N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir E v hfuture
  have hh := hN0 n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir 1 (Or.inl rfl) E v hfuture
  have he (z : Sample cuts) : pileTailCount p v z=RiffleUpperV2.prefixCount (tailBinPrefix E p v) z := by
    rw [← tailBinCount_prefix cuts E p v z]
    unfold pileTailCount tailBinCount
    congr 1
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  simpa only [RiffleLowerV2.falling,Nat.descFactorial_one,he,pow_one,Nat.cast_one,one_mul] using hh



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
      positiveHistory cuts p .backward (j.val+1) ω →
      historyGood cuts D g ξ ε p .backward (j.val+1) ω →
      hasDirection cuts D g .backward (backwardWords cuts p ω j) →
      conditionalExpect (fixedCountPMF cuts)
        (fun z => (wordCount z (backwardWords cuts p ω j)-
          observedCount (backwardWords cuts p ω) (j.val+1) (backwardWords cuts p ω j):ℕ))
        (historyFiber cuts p .backward (j.val+1) ω) ≤
        C1*n*(RiffleLowerV2.wordMass cuts (backwardWords cuts p ω j))^(1-Real.log (1/g)/Real.log (1/τ)) + n*ε := by
  obtain ⟨N0,hN01,hN0⟩ := backward_markedRefinement_current_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT (by linarith)
  let C1 : ℝ := 2/(reserveMass k D g/2)
  have hC1 : 0<C1 := div_pos (by norm_num) (div_pos (reserveMass_pos hk hg) (by norm_num))
  refine ⟨C1,hC1,N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir
  let s := backwardWords cuts p ω j
  let t := observedCount (backwardWords cuts p ω) (j.val+1) s
  let H := historyFiber cuts p .backward (j.val+1) ω
  let b : ℝ := (2*(tailMass cuts L (tailPrefix L s))^(1-Real.log (1/g)/Real.log (1/τ)))/(reserveMass k D g/2)
  have hs : s.get 0=p := backwardWords_first cuts p ω j
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
      positiveHistory cuts p .backward (j.val+1) ω →
      historyGood cuts D g ξ ε p .backward (j.val+1) ω →
      hasDirection cuts D g .backward (backwardWords cuts p ω j) →
      ∀ f : Fin 2 ↪ Fin n, ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → w<backwardWords cuts p ω j) →
      conditionalProbability (fixedCountPMF cuts) (markedCollisionEvent f (tailBinPrefix E p v))
        (historyFiber cuts p .backward (j.val+1) ω) ≤
      (4/((reserveMass k D g)^2/2))*tailExtensionPowerMass cuts (tailBinPrefix E p v)
        (2*(1-Real.log (1/g)/Real.log (1/τ)))*
        conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f)
          (historyFiber cuts p .backward (j.val+1) ω)+ε := by
  obtain ⟨N0,hN01,hN0⟩ := natural_marked_good_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε p ω j hpos hhistory hdir f E v hfuture
  let H := historyFiber cuts p .backward (j.val+1) ω
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



/-- The literal natural-history collision estimate. Its exceptional term is
n² epsilon, without a factor counting possible terminal words. -/
theorem tailCollisions (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1/2) :
    ∃ C2 : ℝ, 0<C2 ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ ε : ℝ, 0≤ε → ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .backward (j.val+1) ω →
      historyGood cuts D g ξ ε p .backward (j.val+1) ω →
      hasDirection cuts D g .backward (backwardWords cuts p ω j) →
      ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → w<backwardWords cuts p ω j) →
      conditionalExpect (fixedCountPMF cuts) (fun z => ∑ w : Word k (L+1),
        if w.toList.take (tailBinPrefix E p v).1.val=(tailBinPrefix E p v).2.toList then
          ((wordCount z w).choose 2:ℝ) else 0)
        (historyFiber cuts p .backward (j.val+1) ω) ≤
        C2*(n:ℝ)^2*(RiffleUpperV2.prefixMass cuts (tailBinPrefix E p v))^(2*(1-Real.log (1/g)/Real.log (1/τ)))*
          tailPowerMass cuts (tailBinPrefix E p v) (2*(1-Real.log (1/g)/Real.log (1/τ)))+(n:ℝ)^2*ε := by
  obtain ⟨N0,hN01,hN0⟩ := natural_markedCollision_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT (by linarith)
  let C2 : ℝ := 4/((reserveMass k D g)^2/2)
  have hC2 : 0<C2 := div_pos (by norm_num) (div_pos (pow_pos (reserveMass_pos hk hg) 2) (by norm_num))
  refine ⟨C2,hC2,N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir E v hfuture
  have hb := fun f => hN0 n hn L hL cuts hn0 hgood ξ ε p ω j hpos hhistory hdir f E v hfuture
  have hsum := collision_expectation_sum_bound cuts p (tailBinPrefix E p v)
    (historyFiber cuts p .backward (j.val+1) ω) hpos
    (C2*tailExtensionPowerMass cuts (tailBinPrefix E p v) (2*(1-Real.log (1/g)/Real.log (1/τ)))) ε hε hb
  apply hsum.trans
  have hnorm := initialPile_collision_normalization cuts hn0 p v (Real.log (1/g)/Real.log (1/τ))
    (rareExponent_nonneg hg hg1 hτ (hτg.trans hg1)) (by linarith)
  rw [extensionPowerMass_eq] at hnorm
  have hh := mul_le_mul_of_nonneg_left hnorm hC2.le
  apply add_le_add _ le_rfl
  convert hh using 1 <;> ring


end RiffleUpperV2.Reservoir.Backward
