import RiffleUpperV2.Conditional.HistoryAdapters
import RiffleUpperV2.Conditional.LinearAveraging
import RiffleUpperV2.Conditional.PrefixAdapters

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir

def historyBlockAverage {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (a : I) (ω : Sample cuts) : ℝ :=
  conditionalExpect (fixedCountPMF cuts)
    (fun v => blockSquares cuts p d (x a) (familyFiber cuts p d j x v))
    (historyFiber cuts p d (j.val+1) ω)

/-- The actual fine-history reduction is averaged back to one natural history.
Auxiliary row sets and margins do not enter the conditioning on the left. -/
theorem historySelfIntersection_family {k n L : ℕ} {I : Type*} [Fintype I]
    (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hpos : positiveHistory cuts p d (j.val+1) ω)
    (hsep : ∀a b,a≠b → prefixSeparated (x a) (x b))
    (hfuture : ∀a w,inCylinder (x a) w → strictFuture d (revealWords cuts p d ω j) w)
    (hcover : ∀w:Word k (L+1),w.get 0=p → strictFuture d (revealWords cuts p d ω j) w → ∃a,inCylinder (x a) w) :
    historySelfIntersection cuts D g p d (j.val+1) ω≤
      conditionalExpect (fixedCountPMF cuts) (currentExcess cuts p d j ω)
        (historyFiber cuts p d (j.val+1) ω)+∑a,historyBlockAverage cuts p d j x a ω := by
  let Z := futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x
  let U := naturalHistory cuts p d (j.val+1)
  let H := historyFiber cuts p d (j.val+1) ω
  have hj := selfIntersectionJensen_expect (fixedCountPMF cuts) Z U Prod.fst (fun _ => rfl)
    (U ω) hpos (remainingEdgeEvent cuts D g p d (j.val+1))
  apply hj.trans
  have hm : conditionalExpect (fixedCountPMF cuts)
      (fun v => ∑e,(conditionalProbability (fixedCountPMF cuts)
        (remainingEdgeEvent cuts D g p d (j.val+1) e) (fun z => Z z=Z v))^2) H≤
    conditionalExpect (fixedCountPMF cuts)
      (fun v => conditionalExpect (fixedCountPMF cuts) (currentExcess cuts p d j ω) (fun z => Z z=Z v)+
        ∑a,blockSquares cuts p d (x a) (familyFiber cuts p d j x v)) H := by
    apply conditionalExpect_mono_on
    intro v hv
    have hs := currentWord_history cuts p d j ω v hv
    have hh := fineSelfIntersection_le cuts D g p d v j x hsep
      (by simpa only [hs] using hfuture) (by simpa only [hs] using hcover)
    simpa only [familyFiber_on_history cuts p d j x ω v hv,currentExcess_on_history cuts p d j ω v hv,Z]
      using hh
  apply hm.trans_eq
  rw [conditionalExpect_add,conditionalExpect_sum]
  exact congrArg (fun z:ℝ => z+∑a,historyBlockAverage cuts p d j x a ω)
    (conditionalExpect_tower (fixedCountPMF cuts) Z U Prod.fst (fun _ => rfl) (U ω) hpos (currentExcess cuts p d j ω))

theorem historyBlockAverage_le_count {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (a : I) (ω : Sample cuts) (hpos : positiveHistory cuts p d (j.val+1) ω) :
    historyBlockAverage cuts p d j x a ω≤conditionalExpect (fixedCountPMF cuts)
      (fun v => (RiffleUpperV2.prefixCount (x a) v:ℝ)) (historyFiber cuts p d (j.val+1) ω) := by
  let Z := futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x
  let U := naturalHistory cuts p d (j.val+1)
  have ht := conditionalExpect_tower (fixedCountPMF cuts) Z U Prod.fst (fun _ => rfl) (U ω) hpos
    (fun v => (RiffleUpperV2.prefixCount (x a) v:ℝ))
  apply le_trans ?_ ht.le
  apply conditionalExpect_mono_on
  intro v hv
  have hh := blockSquares_le_count cuts p d (x a) (familyFiber cuts p d j x v)
  simpa only [familyFiber_on_history cuts p d j x ω v hv,Z] using hh

theorem historyBlockAverage_le_collisions {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (a : I) (ω : Sample cuts) (hpos : positiveHistory cuts p d (j.val+1) ω) :
    historyBlockAverage cuts p d j x a ω≤conditionalExpect (fixedCountPMF cuts)
      (fun v => ∑w:Word k (L+1),if inCylinder (x a) w then ((wordCount v w).choose 2:ℝ) else 0)
      (historyFiber cuts p d (j.val+1) ω) := by
  let Z := futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x
  let U := naturalHistory cuts p d (j.val+1)
  have ht := conditionalExpect_tower (fixedCountPMF cuts) Z U Prod.fst (fun _ => rfl) (U ω) hpos
    (fun v => ∑w:Word k (L+1),if inCylinder (x a) w then ((wordCount v w).choose 2:ℝ) else 0)
  apply le_trans ?_ ht.le
  apply conditionalExpect_mono_on
  intro v hv
  have hh := blockSquares_le_collisions cuts p d (x a) (familyFiber cuts p d j x v)
  simpa only [familyFiber_on_history cuts p d j x ω v hv,Z,←inCylinder_iff_take] using hh

/-- A large-block first moment on H costs only the natural history's single
bad-event probability when the auxiliary information is averaged away. -/
theorem historyBlockAverage_large {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ ε b : ℝ) (hb : 0≤b) (p : Fin k) (d : Direction)
    (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1)) (a : I) (ω : Sample cuts)
    (hpos : positiveHistory cuts p d (j.val+1) ω)
    (hgood : historyGood cuts D g ξ ε p d (j.val+1) ω)
    (hsep : ∀a b,a≠b → prefixSeparated (x a) (x b))
    (hfuture : ∀w,inCylinder (x a) w → strictFuture d (revealWords cuts p d ω j) w)
    (hF : ∀v:Sample cuts,concentrationEvent cuts D g ξ v →
      expectedCommonEdges (inducedCuts cuts (cylinderRows (x a) v) (x a) v)≤b) :
    historyBlockAverage cuts p d j x a ω≤b+n*ε := by
  have hm : historyBlockAverage cuts p d j x a ω≤conditionalExpect (fixedCountPMF cuts)
      (fun v => b+(n:ℝ)*(if ¬concentrationEvent cuts D g ξ v then 1 else 0))
      (historyFiber cuts p d (j.val+1) ω) := by
    apply conditionalExpect_mono_on
    intro v hv
    by_cases hH : concentrationEvent cuts D g ξ v
    · simp only [hH,not_true_eq_false,if_false,mul_zero,add_zero]
      exact (fineBlockSquares_le_firstMoment cuts p d v j x hsep a
        (by simpa only [currentWord_history cuts p d j ω v hv] using hfuture)).trans (hF v hH)
    · simp only [hH,not_false_eq_true,if_true,mul_one]
      exact (blockSquares_le_n cuts p d (x a) (familyFiber cuts p d j x v)).trans (by linarith)
  rw [conditionalExpect_bad_cost _ _ _ hpos] at hm
  exact hm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgood (Nat.cast_nonneg n)))

end RiffleUpperV2.Conditional
