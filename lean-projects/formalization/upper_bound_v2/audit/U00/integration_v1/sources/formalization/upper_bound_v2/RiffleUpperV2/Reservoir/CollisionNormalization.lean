import RiffleUpperV2.Reservoir.CollisionEvents

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

def tailExtensionPowerMass {k n L : ℕ} (cuts : Cuts k n (L+1)) (x : Prefix k (L+1)) (q : ℝ) : ℝ :=
  ∑ w : Word k (L+1), if w.toList.take x.1.val=x.2.toList then
    tailMass cuts L (tailPrefix L w)^q else 0

theorem initialPile_collision_normalization {k n L E : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0<n) (p : Fin k) (v : Word k (min E L)) (α : ℝ) (hα0 : 0≤α) (hα1 : α≤1) :
    RiffleLowerV2.falling (pileSize cuts p) 2 * tailExtensionPowerMass cuts (tailBinPrefix E p v) (2*(1-α)) ≤
      (n:ℝ)^2 * extensionPowerMass cuts (tailBinPrefix E p v) (2*(1-α)) := by
  unfold tailExtensionPowerMass extensionPowerMass
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : w.toList.take (tailBinPrefix E p v).1.val=(tailBinPrefix E p v).2.toList
  · simp only [if_pos hw]
    have hp : w.get 0=p := ((tailBinPrefix_word E p v w).mp hw).1
    have h := initialPile_normalization (m := 2) hn
      (show pileSize cuts p≤n by have := pileOffset_add_size_le cuts p; omega)
      (q := tailMass cuts L (tailPrefix L w)) (by unfold tailMass; positivity) hα0 hα1
    have he := pileTailMass_eq_prefixMass cuts p (tailPrefix L w)
    rw [← hp,tailBinPrefix_full] at he
    change ((pileSize cuts (w.get 0):ℝ)/n)*tailMass cuts L (tailPrefix L w)=RiffleLowerV2.wordMass cuts w at he
    rw [hp] at he
    rw [he] at h
    simpa only [Nat.cast_ofNat] using h
  · simp only [hw,if_false,mul_zero,le_refl]

end RiffleUpperV2.Reservoir
