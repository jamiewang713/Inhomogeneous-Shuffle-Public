import RiffleUpperV2.Reservoir.DeletionPrefix
import RiffleUpperV2.Reservoir.FullTail
import RiffleUpperV2.Reservoir.SupportBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

def markedCurrentEvent {k n L : ℕ} {cuts : Cuts k n (L+1)} (f : Fin 1 ↪ Fin n)
    (s : Word k (L+1)) (t : ℕ) (ω : Sample cuts) : Prop :=
  (∀ i, rowWord ω (f i)=s) ∧ t≤wordCount ω s-1

theorem markedRefinement_current_upper_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ : ℝ, ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      ∀ f : Fin 1 ↪ Fin n, ∀ ω₀ : Sample cuts,
      historyFiber cuts p .forward (j.val+1) ω ω₀ → markedPileEvent p f ω₀ →
      goodMarkedView cuts D g ξ p (Finset.univ.map f) ω₀ →
      conditionalProbability (fixedCountPMF cuts)
        (markedCurrentEvent f (pileWords cuts p ω j)
          (observedCount (pileWords cuts p ω) (j.val+1) (pileWords cuts p ω j)))
        (fun z => markedRefinement cuts p (j.val+1) (Finset.univ.map f) z=
          markedRefinement cuts p (j.val+1) (Finset.univ.map f) ω₀) ≤
        (2*(tailMass cuts L (tailPrefix L (pileWords cuts p ω j)))^(1-Real.log (1/g)/Real.log (1/τ))) /
          (reserveMass k D g/2) := by
  obtain ⟨N0,hN01,hN0⟩ := history_deletionPrefix_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ p ω j hdir f ω₀ hhist hsupport hG
  let s := pileWords cuts p ω j
  let t := observedCount (pileWords cuts p ω) (j.val+1) s
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
  have hdelete : ∀ z, pileBase cuts p e A a z → historyFiber cuts p .forward (j.val+1) ω z →
      Target z → unmarkedHistoryConstraint cuts p ω j A a := by
    intro z hB hH hz
    apply unmarkedHistoryConstraint_of_current_removal cuts p ω j A a (tupleWords e z)
      hcard hB.2 ((tupleHistoryConstraint_iff cuts p e ω z j).mpr ⟨hB.1,hH⟩) (hmarked z hz)
    have hsfirst : s.get 0=p := pileWords_first cuts p ω j
    have hr := hz.2
    rw [tuplePile_wordCount cuts p e z hB.1 s hsfirst] at hr
    exact hr
  have hbound := hN0 n hn L hL cuts hn0 hgood ξ p e ω j hdir A a (Or.inl hcard)
    z₀ hbase hHz₀ L (tailPrefix L s) Target hprefix hdelete
  rw [hcard] at hbound
  have hevent : (fun z : Sample cuts => markedRefinement cuts p (j.val+1) M z=
      markedRefinement cuts p (j.val+1) M ω₀) =
      (fun z => pileBase cuts p e A a z ∧ historyFiber cuts p .forward (j.val+1) ω z) := by
    funext z
    apply propext
    rw [markedRefinement_fiber]
    change _ ∧ naturalHistory cuts p .forward (j.val+1) z=naturalHistory cuts p .forward (j.val+1) ω₀ ↔ _
    rw [hhist]
    rfl
  change conditionalProbability (fixedCountPMF cuts) Target
    (fun z => markedRefinement cuts p (j.val+1) M z=markedRefinement cuts p (j.val+1) M ω₀) ≤ _
  rw [hevent]
  simpa only [pow_one,Nat.cast_one,one_mul] using hbound

end RiffleUpperV2.Reservoir
