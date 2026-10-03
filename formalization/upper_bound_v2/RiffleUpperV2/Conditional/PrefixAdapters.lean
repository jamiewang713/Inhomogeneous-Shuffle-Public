import RiffleUpperV2.Conditional.FutureCylinders
import RiffleUpperV2.Exploration.GuardConcentration

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open Exploration TimeProfile RiffleLowerV2.Thinning

/-- The unrestricted cylinder convention agrees with the actual count predicate. -/
theorem inCylinder_iff_take {k K : ℕ} (x : Prefix k K) (w : Word k K) :
    inCylinder x w ↔ w.toList.take x.1.val=x.2.toList := by
  simp only [inCylinder,List.prefix_iff_eq_take,List.Vector.toList_length,eq_comm]

/-- Every prefix has a literal full-word extension, including zero-mass words. -/
theorem inCylinder_exists {k K : ℕ} (p : Fin k) (x : Prefix k K) :
    ∃ w : Word k K, inCylinder x w := by
  let w : Word k K := List.Vector.ofFn (fun j => if h : j.val<x.1.val then x.2.get ⟨j.val,h⟩ else p)
  refine ⟨w,(inCylinder_iff_take x w).mpr ?_⟩
  apply (vector_take_eq_iff (Nat.le_of_lt_succ x.1.isLt) w x.2).mpr
  intro j
  simp [w,Fin.castLE,j.isLt]

/-- A nonroot cylinder contained in pile p has first prefix digit p. -/
theorem prefixFirst_of_cylinder {k L : ℕ} (p : Fin k) (x : Prefix k (L+1))
    (hx : 0<x.1.val) (hp : ∀ w : Word k (L+1), inCylinder x w → w.get 0=p) :
    x.2.get ⟨0,hx⟩=p := by
  obtain ⟨w,hw⟩ := inCylinder_exists p x
  have hc := (vector_take_eq_iff (Nat.le_of_lt_succ x.1.isLt) w x.2).mp
    ((inCylinder_iff_take x w).mp hw) ⟨0,hx⟩
  exact hc.symm.trans (hp w hw)

/-- Constructive adapter: the actual tail prefix has length |x|-1. -/
theorem tailBinPrefix_of_first {k L : ℕ} (p : Fin k) (x : Prefix k (L+1))
    (hx : 0<x.1.val) (hp : x.2.get ⟨0,hx⟩=p) :
    ∃ v : Word k (min (x.1.val-1) L), tailBinPrefix (x.1.val-1) p v=x := by
  obtain ⟨w,hw⟩ := inCylinder_exists p x
  have htake := (inCylinder_iff_take x w).mp hw
  have hc := (vector_take_eq_iff (Nat.le_of_lt_succ x.1.isLt) w x.2).mp htake ⟨0,hx⟩
  have hwp : w.get 0=p := hc.trans hp
  refine ⟨tailPrefix (x.1.val-1) w,?_⟩
  apply prefix_ext
  have hbin := (tailBinPrefix_word (x.1.val-1) p (tailPrefix (x.1.val-1) w) w).mpr ⟨hwp,rfl⟩
  have hlen : min (x.1.val-1) L+1=x.1.val := by have := x.1.isLt; omega
  change (List.Vector.cons p (tailPrefix (x.1.val-1) w)).toList=x.2.toList
  rw [← hbin,hlen]
  exact htake

/-- Arbitrary actual cylinders contained in one first pile fit the reservoir API. -/
theorem tailBinPrefix_of_cylinder {k L : ℕ} (p : Fin k) (x : Prefix k (L+1))
    (hx : 0<x.1.val) (hp : ∀ w : Word k (L+1), inCylinder x w → w.get 0=p) :
    ∃ E : ℕ, ∃ v : Word k (min E L), tailBinPrefix E p v=x := by
  obtain ⟨v,hv⟩ := tailBinPrefix_of_first p x hx (prefixFirst_of_cylinder p x hx hp)
  exact ⟨x.1.val-1,v,hv⟩

/-- The primitive reservoir tail-word conditions give membership in the exact cylinder. -/
theorem inCylinder_tailBinPrefix {k L : ℕ} (E : ℕ) (p : Fin k)
    (v : Word k (min E L)) (w : Word k (L+1)) :
    inCylinder (tailBinPrefix E p v) w ↔ w.get 0=p ∧ tailPrefix E w=v := by
  rw [inCylinder_iff_take]
  exact tailBinPrefix_word E p v w

end RiffleUpperV2.Conditional
