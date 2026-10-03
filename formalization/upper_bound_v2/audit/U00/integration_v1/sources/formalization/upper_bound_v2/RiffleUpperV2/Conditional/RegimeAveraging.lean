import RiffleUpperV2.Conditional.HistoryAveraging
import RiffleUpperV2.Conditional.SmallCylinderBounds
import RiffleUpperV2.Conditional.LargeFirstMoment

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir TimeProfile

/-- All three actual cylinder regimes have one uniform natural-history bound.
The large regime uses the proved induced F theorem and averages out H. -/
theorem regimeBlockAverage_uniform (k D : ℕ) (hk : 2≤k) (hD : 1≤D)
    (T η g τ : ℝ) (hT : 0<T) (hη : 0<η) (hg : 0<g) (hgK : g<1/(k:ℝ))
    (hτ : 0<τ) (hτg : τ<g)
    (hα : Real.log (1/g)/Real.log (1/τ)<1/2)
    (hαtiny : Real.log (1/g)/Real.log (1/τ)≤(η/10)/(4*(1+η/10)))
    (hαinter : Real.log (1/g)/Real.log (1/τ)≤η/(40*(1+η))) :
    ∃Csum:ℝ,0<Csum ∧ ∃N0:ℕ,2≤N0 ∧ ∀N:ℕ,N0≤N → ∀L:ℕ,
      ∀cuts:Cuts k N (L+1),∀hN:0<N,
      ((L+1:ℕ):ℝ)≤T*Real.log (N:ℝ) → GoodColumn (cuts.profile hN 0) g →
      EmpiricalNegativeMargin N 0 cuts hN (2*η) →
      ∀ε:ℝ,0≤ε → ∀p:Fin k,∀d:Direction,∀ω:Sample cuts,∀j:Fin (pileSize cuts p),
      positiveHistory cuts p d (j.val+1) ω → historyGood cuts D g (η/10) ε p d (j.val+1) ω →
      hasDirection cuts D g d (revealWords cuts p d ω j) →
      ∀(I:Type) [Fintype I],∀x:I→Prefix k (L+1),
      (∀a b,a≠b → prefixSeparated (x a) (x b)) →∀a:I,
      0<(x a).1.val → (∀w,inCylinder (x a) w → w.get 0=p) →
      (∀w,inCylinder (x a) w → strictFuture d (revealWords cuts p d ω j) w) →
      (prefixMean cuts (x a)<(N:ℝ)^(-(η/10)) ∨
        ∃c:Fin (L+1),c.val=(x a).1.val ∧ GoodColumn (cuts.profile hN c) g) →
      historyBlockAverage cuts p d j x a ω≤
        Csum*(N:ℝ)^(-decayBudget η (η/8))+2*(N:ℝ)^2*ε := by
  have hk0 : 0<k := by omega
  have hkr : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hg1 : g<1 := hgK.trans_le ((div_le_one (by positivity : (0:ℝ)<k)).mpr hkr)
  obtain ⟨Ct,hCt,Nt,hNt,ht⟩ := tinyCylinder_count k D hk0 hD g τ T hg hg1 hτ hτg hT hα
  obtain ⟨Ci,hCi,Ni,hNi,hi⟩ := intermediateCylinder_collisions k D hk0 hD g τ T hg hg1 hτ hτg hT hα
  obtain ⟨Nl,hNl,hl⟩ := largeCylinder_firstMoment k hk T η g hT hη hg hgK
  refine ⟨Ct+Ci+1,by linarith,Nt+Ni+Nl,by omega,?_⟩
  intro N hNN L cuts hN hL hfirst hmargin ε hε p d ω j hpos hhistory hdir I _ x hsep a hx hp hfuture hprepared
  have hN2 : 2≤N := by omega
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hNr0 : (0:ℝ)<N := by exact_mod_cast hN
  have hβ : empiricalBeta N 0 cuts hN (L+1)≤-η := by
    have hh := hmargin.1
    simp only [zero_add] at hh
    linarith
  have hα0 := rareExponent_nonneg hg hg1 hτ (hτg.trans hg1)
  have hab := decayBudget_bounds η (η/8)
  have herror : (N:ℝ)*ε≤2*(N:ℝ)^2*ε := by
    have hsq : (N:ℝ)≤2*(N:ℝ)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq hε
  have herror2 : (N:ℝ)^2*ε≤2*(N:ℝ)^2*ε := by nlinarith [mul_nonneg (sq_nonneg (N:ℝ)) hε]
  have hcoefft : Ct≤Ct+Ci+1 := by linarith
  have hcoeffi : Ci≤Ct+Ci+1 := by linarith
  by_cases htiny : prefixMean cuts (x a)≤(N:ℝ)^(-(η/10))
  · have hh := ht N (by omega) L hL cuts hN hfirst (η/10) ε hε p d ω j hpos hhistory hdir (x a) hx hp hfuture htiny
    have hpow : (N:ℝ)^(-(η/10)+(Real.log (1/g)/Real.log (1/τ))*(1+η/10))≤
        (N:ℝ)^(-decayBudget η (η/8)) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith [tinyExponent_budget (by positivity : 0<η/10) hαtiny,hab.1])
    exact (historyBlockAverage_le_count cuts p d j x a ω hpos).trans
      (hh.trans (add_le_add (mul_le_mul hcoefft hpow (Real.rpow_nonneg hNr0.le _) (by linarith)) herror))
  · by_cases hinter : prefixMean cuts (x a)≤(N:ℝ)^(η/10)
    · have hh := hi N (by omega) L hL cuts hN hfirst (η/10) η ε hε p d ω j hpos hhistory hdir (x a) hx hp hfuture
        (le_of_not_ge htiny) hinter hβ
      have hpow : (N:ℝ)^(-η+3*(η/10)+2*(Real.log (1/g)/Real.log (1/τ))*(1+η-2*(η/10)))≤
          (N:ℝ)^(-decayBudget η (η/8)) := Real.rpow_le_rpow_of_exponent_le hNr
        (by linarith [intermediateExponent_budget hη hα0 hαinter,hab.2.1])
      exact (historyBlockAverage_le_collisions cuts p d j x a ω hpos).trans
        (hh.trans (add_le_add (mul_le_mul hcoeffi hpow (Real.rpow_nonneg hNr0.le _) (by linarith)) herror2))
    · have hnext : ∃c:Fin (L+1),c.val=(x a).1.val ∧ GoodColumn (cuts.profile hN c) g :=
        hprepared.resolve_left (fun h => htiny h.le)
      have hlarge : (N:ℝ)^(η/10)≤prefixMean cuts (x a) := le_of_not_ge hinter
      have hh := historyBlockAverage_large cuts D g (η/10) ε ((N:ℝ)^(-η/8))
        (Real.rpow_nonneg hNr0.le _) p d j x a ω hpos hhistory hsep hfuture
        (fun v hv => hl N (by omega) L cuts D (x a) v hL hmargin hv hlarge hnext)
      apply hh.trans
      apply add_le_add _ herror
      have hpow : (N:ℝ)^(-η/8)≤(N:ℝ)^(-decayBudget η (η/8)) := by
        apply Real.rpow_le_rpow_of_exponent_le hNr
        linarith [hab.2.2]
      exact hpow.trans ((le_mul_iff_one_le_left (Real.rpow_pos_of_pos hNr0 _)).mpr (by linarith))

end RiffleUpperV2.Conditional
