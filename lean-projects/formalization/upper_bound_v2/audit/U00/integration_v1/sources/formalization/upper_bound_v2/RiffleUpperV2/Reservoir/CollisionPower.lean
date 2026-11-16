import RiffleUpperV2.Localization.CollisionMass
import RiffleUpperV2.Reservoir.ExtraCopies

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration RiffleUpperV2.Localization
attribute [local instance 2000] wordDecEq

def extensionPowerMass {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) (q : ℝ) : ℝ :=
  ∑ w : Word k d, if w.toList.take x.1.val=x.2.toList then RiffleLowerV2.wordMass cuts w^q else 0

def tailPowerMass {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) (q : ℝ) : ℝ :=
  ∏ j : Fin d, if j.val<x.1.val then 1 else ∑ a : Fin k, ((cuts.count j a:ℝ)/n)^q

theorem extensionPowerMass_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) (q : ℝ) :
    extensionPowerMass cuts x q = (prefixMass cuts x)^q * tailPowerMass cuts x q := by
  let f : Fin d → Fin k → ℝ := fun j a =>
    if a ∈ prefixDigits x j then ((cuts.count j a : ℝ)/n)^q else 0
  have hw (w : Word k d) :
      (if w.toList.take x.1.val=x.2.toList then RiffleLowerV2.wordMass cuts w^q else 0) =
        ∏ j : Fin d, f j (w.get j) := by
    by_cases h : ∀ j : Fin d, w.get j ∈ prefixDigits x j
    · rw [if_pos ((word_prefixDigits_iff x w).mp h),GraphOverlap.wordMass_eq_prod,
        ← Real.finsetProd_rpow _ _ (by intros; positivity)]
      exact Finset.prod_congr rfl (fun j _ => by simp [f,h j])
    · rw [if_neg (fun hh => h ((word_prefixDigits_iff x w).mpr hh))]
      obtain ⟨j,hj⟩ := not_forall.mp h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [f,hj])).symm
  unfold extensionPowerMass
  simp_rw [hw]
  have hs := (Equiv.vectorEquivFin (Fin k) d).sum_comp (fun w : Fin d → Fin k => ∏ j, f j (w j))
  change (∑ w : Word k d, ∏ j, f j (w.get j)) = _ at hs
  rw [hs,← Fintype.prod_sum f]
  change _ = (RiffleLowerV2.prefixMass cuts x)^q * _
  unfold tailPowerMass
  rw [← RiffleLowerV2.Thinning.prefixColumnFraction_product,← Real.finsetProd_rpow _ _ (by
    intro j _
    unfold RiffleLowerV2.Thinning.prefixColumnFraction
    split_ifs <;> positivity),← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  change (∑ a : Fin k, f j a) = _ * (if j.val < x.1.val then 1 else _)
  unfold RiffleLowerV2.Thinning.prefixColumnFraction
  by_cases hj : j.val < x.1.val
  · simp [f,prefixDigits,hj]
  · simp [f,prefixDigits,hj]


end RiffleUpperV2.Reservoir
