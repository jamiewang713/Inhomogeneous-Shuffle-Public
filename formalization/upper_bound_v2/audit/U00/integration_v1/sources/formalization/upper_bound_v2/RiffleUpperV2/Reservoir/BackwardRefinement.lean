import RiffleUpperV2.Reservoir.BackwardRestricted
import RiffleUpperV2.Reservoir.CurrentMarked

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

def backwardMarkedRefinement {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (i : ℕ)
    (M : Finset (Fin n)) (ω : Sample cuts) :=
  (naturalHistory cuts p .backward i ω, exposedPileView p M ω)

theorem backward_markedRefinement_fiber {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (i : ℕ) (M : Finset (Fin n)) (ω₀ z : Sample cuts) :
    backwardMarkedRefinement cuts p i M z=backwardMarkedRefinement cuts p i M ω₀ ↔
      pileBase cuts p (pileEnumeration cuts p ω₀) (unmarkedIndices (pileEnumeration cuts p ω₀) M)
        (tupleWords (pileEnumeration cuts p ω₀) ω₀) z ∧ historyFiber cuts p .backward i ω₀ z := by
  rw [Prod.mk.injEq]
  change historyFiber cuts p .backward i ω₀ z ∧ exposedPileView p M z=exposedPileView p M ω₀ ↔ _
  rw [exposedPileView_eq_iff cuts p M (pileEnumeration cuts p ω₀) ω₀ z (pileEnumeration_first cuts p ω₀)]
  exact and_comm

/-- A positive fine history is an actual labeled-pile/unmarked-row base
intersected with the original history. The rare/regular estimate transfers
to fixed original labels, without adding these labels to the natural history. -/
theorem backward_markedRefinement_prefix_upper_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ : ℝ, ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      hasDirection cuts D g .backward (backwardWords cuts p ω j) →
      ∀ m : ℕ, (m=1 ∨ m=2) → ∀ f : Fin m ↪ Fin n, ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → w<backwardWords cuts p ω j) →
      ∀ ω₀ : Sample cuts, historyFiber cuts p .backward (j.val+1) ω ω₀ →
      markedPileEvent p f ω₀ → goodMarkedView cuts D g ξ p (Finset.univ.map f) ω₀ →
      conditionalProbability (fixedCountPMF cuts) (markedTailEvent p f v)
        (fun z => backwardMarkedRefinement cuts p (j.val+1) (Finset.univ.map f) z=
          backwardMarkedRefinement cuts p (j.val+1) (Finset.univ.map f) ω₀) ≤
        (2^m*(tailMass cuts E v)^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))) /
          ((reserveMass k D g)^m/2) := by
  obtain ⟨N0,hN01,hN0⟩ := backward_history_prefixProbability_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ p ω j hdir m hm f E v hfuture ω₀ hhist hsupport hG
  let M := Finset.univ.map f
  let e := pileEnumeration cuts p ω₀
  let A := unmarkedIndices e M
  let a := tupleWords e ω₀
  have he : ∀ q, (tupleWords e ω₀ q).get 0=p := pileEnumeration_first cuts p ω₀
  have hf : ∀ i, ∃ q, e q=f i := fun i => (tuplePile_exhausts cuts p e ω₀ he (f i)).mp (hsupport i)
  have hcard : (Finset.univ \ A).card=m := by
    rw [unmarkedIndices_card_compl e M (by
      intro r hr
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hr
      exact hf i)]
    simp [M]
  obtain ⟨z₀,hz₀,hHz₀⟩ := hG
  have hbase : pileBase cuts p e A a z₀ := (exposedPileView_eq_iff cuts p M e ω₀ z₀ he).mp hz₀
  have hbound := hN0 n hn L hL cuts hn0 hgood ξ p e ω j hdir A a (by rwa [hcard])
    z₀ hbase hHz₀ E v hfuture
  rw [hcard] at hbound
  have hevent : (fun z : Sample cuts => backwardMarkedRefinement cuts p (j.val+1) M z=
      backwardMarkedRefinement cuts p (j.val+1) M ω₀) =
      (fun z => pileBase cuts p e A a z ∧ historyFiber cuts p .backward (j.val+1) ω z) := by
    funext z
    apply propext
    rw [backward_markedRefinement_fiber]
    change _ ∧ naturalHistory cuts p .backward (j.val+1) z=naturalHistory cuts p .backward (j.val+1) ω₀ ↔ _
    rw [hhist]
    rfl
  change conditionalProbability (fixedCountPMF cuts) (markedTailEvent p f v)
    (fun z => backwardMarkedRefinement cuts p (j.val+1) M z=backwardMarkedRefinement cuts p (j.val+1) M ω₀) ≤ _
  rw [hevent]
  apply le_trans _ hbound
  apply conditionalProbability_mono_on
  intro z _ hz
  exact (markedPrefix_reindex cuts p e f hf E v z).mp hz.2

theorem backward_markedRefinement_current_upper_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ : ℝ, ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      hasDirection cuts D g .backward (backwardWords cuts p ω j) →
      ∀ f : Fin 1 ↪ Fin n, ∀ ω₀ : Sample cuts,
      historyFiber cuts p .backward (j.val+1) ω ω₀ → markedPileEvent p f ω₀ →
      goodMarkedView cuts D g ξ p (Finset.univ.map f) ω₀ →
      conditionalProbability (fixedCountPMF cuts)
        (markedCurrentEvent f (backwardWords cuts p ω j)
          (observedCount (backwardWords cuts p ω) (j.val+1) (backwardWords cuts p ω j)))
        (fun z => backwardMarkedRefinement cuts p (j.val+1) (Finset.univ.map f) z=
          backwardMarkedRefinement cuts p (j.val+1) (Finset.univ.map f) ω₀) ≤
        (2*(tailMass cuts L (tailPrefix L (backwardWords cuts p ω j)))^(1-Real.log (1/g)/Real.log (1/τ))) /
          (reserveMass k D g/2) := by
  obtain ⟨N0,hN01,hN0⟩ := backward_history_deletionPrefix_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ p ω j hdir f ω₀ hhist hsupport hG
  let s := backwardWords cuts p ω j
  let t := observedCount (backwardWords cuts p ω) (j.val+1) s
  let Target : Sample cuts → Prop := markedCurrentEvent f s t
  let M := Finset.univ.map f
  let e := pileEnumeration cuts p ω₀
  let A := unmarkedIndices e M
  let a := tupleWords e ω₀
  have he : ∀ q, (tupleWords e ω₀ q).get 0=p := pileEnumeration_first cuts p ω₀
  have hf : ∀ i, ∃ q, e q=f i := fun i => (tuplePile_exhausts cuts p e ω₀ he (f i)).mp (hsupport i)
  have hcard : (Finset.univ \ A).card=1 := by
    rw [unmarkedIndices_card_compl e M (by
      intro r hr
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hr
      exact hf i)]
    simp [M]
  obtain ⟨z₀,hz₀,hHz₀⟩ := hG
  have hbase : pileBase cuts p e A a z₀ := (exposedPileView_eq_iff cuts p M e ω₀ z₀ he).mp hz₀
  have hmarked (z : Sample cuts) (hz : Target z) : ∀ q, q∉A → tupleWords e z q=s := by
    intro q hq
    have hmem : e q∈M := by simpa only [A,unmarkedIndices,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hq
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hmem
    change rowWord z (e q)=s
    rw [← hi]
    exact hz.1 i
  have hprefix : ∀ z, pileBase cuts p e A a z → Target z →
      ∀ q, q∉A → tailPrefix L (tupleWords e z q)=tailPrefix L s := by
    intro z _ hz q hq
    rw [hmarked z hz q hq]
  have hdelete : ∀ z, pileBase cuts p e A a z → historyFiber cuts p .backward (j.val+1) ω z →
      Target z → backwardUnmarkedHistoryConstraint cuts p ω j A a := by
    intro z hB hH hz
    apply backwardUnmarkedHistoryConstraint_of_current_removal cuts p ω j A a (tupleWords e z)
      hcard hB.2 ((backwardTupleHistoryConstraint_iff cuts p e ω z j).mpr ⟨hB.1,hH⟩) (hmarked z hz)
    have hsfirst : s.get 0=p := backwardWords_first cuts p ω j
    have hr := hz.2
    rw [tuplePile_wordCount cuts p e z hB.1 s hsfirst] at hr
    exact hr
  have hbound := hN0 n hn L hL cuts hn0 hgood ξ p e ω j hdir A a (Or.inl hcard)
    z₀ hbase hHz₀ L (tailPrefix L s) Target hprefix hdelete
  rw [hcard] at hbound
  have hevent : (fun z : Sample cuts => backwardMarkedRefinement cuts p (j.val+1) M z=
      backwardMarkedRefinement cuts p (j.val+1) M ω₀) =
      (fun z => pileBase cuts p e A a z ∧ historyFiber cuts p .backward (j.val+1) ω z) := by
    funext z
    apply propext
    rw [backward_markedRefinement_fiber]
    change _ ∧ naturalHistory cuts p .backward (j.val+1) z=naturalHistory cuts p .backward (j.val+1) ω₀ ↔ _
    rw [hhist]
    rfl
  change conditionalProbability (fixedCountPMF cuts) Target
    (fun z => backwardMarkedRefinement cuts p (j.val+1) M z=backwardMarkedRefinement cuts p (j.val+1) M ω₀) ≤ _
  rw [hevent]
  simpa only [pow_one,Nat.cast_one,one_mul] using hbound

end RiffleUpperV2.Reservoir
