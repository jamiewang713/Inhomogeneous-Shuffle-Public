import RiffleUpperV2.Reservoir.CollisionConditional

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

/-- The literal natural-history collision estimate. Its exceptional term is
n² epsilon, without a factor counting possible terminal words. -/
theorem tailCollisions (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1/2) :
    ∃ C2 : ℝ, 0<C2 ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ ε : ℝ, 0≤ε → ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .forward (j.val+1) ω →
      historyGood cuts D g ξ ε p .forward (j.val+1) ω →
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → pileWords cuts p ω j<w) →
      conditionalExpect (fixedCountPMF cuts) (fun z => ∑ w : Word k (L+1),
        if w.toList.take (tailBinPrefix E p v).1.val=(tailBinPrefix E p v).2.toList then
          ((wordCount z w).choose 2:ℝ) else 0)
        (historyFiber cuts p .forward (j.val+1) ω) ≤
        C2*(n:ℝ)^2*(RiffleUpperV2.prefixMass cuts (tailBinPrefix E p v))^(2*(1-Real.log (1/g)/Real.log (1/τ)))*
          tailPowerMass cuts (tailBinPrefix E p v) (2*(1-Real.log (1/g)/Real.log (1/τ)))+(n:ℝ)^2*ε := by
  obtain ⟨N0,hN01,hN0⟩ := natural_markedCollision_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT (by linarith)
  let C2 : ℝ := 4/((reserveMass k D g)^2/2)
  have hC2 : 0<C2 := div_pos (by norm_num) (div_pos (pow_pos (reserveMass_pos hk hg) 2) (by norm_num))
  refine ⟨C2,hC2,N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir E v hfuture
  have hb := fun f => hN0 n hn L hL cuts hn0 hgood ξ ε p ω j hpos hhistory hdir f E v hfuture
  have hsum := collision_expectation_sum_bound cuts p (tailBinPrefix E p v)
    (historyFiber cuts p .forward (j.val+1) ω) hpos
    (C2*tailExtensionPowerMass cuts (tailBinPrefix E p v) (2*(1-Real.log (1/g)/Real.log (1/τ)))) ε hε hb
  apply hsum.trans
  have hnorm := initialPile_collision_normalization cuts hn0 p v (Real.log (1/g)/Real.log (1/τ))
    (rareExponent_nonneg hg hg1 hτ (hτg.trans hg1)) (by linarith)
  rw [extensionPowerMass_eq] at hnorm
  have hh := mul_le_mul_of_nonneg_left hnorm hC2.le
  apply add_le_add _ le_rfl
  convert hh using 1 <;> ring

end RiffleUpperV2.Reservoir
