import RiffleUpperV2.Conditional.RegimeAveraging
import RiffleUpperV2.Conditional.PreparedFamily
import RiffleUpperV2.Conditional.CurrentRunBound
import RiffleUpperV2.Conditional.ConditionalScale

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir TimeProfile

/-- The concrete one-natural-history bound after all model, reservoir,
refinement, good-event and first-moment premises have been discharged. -/
theorem oneHistory_uniform (k D : ℕ) (hk : 2≤k) (hD : 1≤D)
    (T η g γ τ ρ A cH : ℝ) (hT : 0<T) (hη : 0<η) (hg : 0<g) (hgK : g<1/(k:ℝ))
    (hγ : 0<γ) (hγ1 : γ≤1) (hτ : 0<τ) (hτg : τ<g) (hρ : 0<ρ) (hcH : 0<cH)
    (hα : Real.log (1/g)/Real.log (1/τ)<1/2)
    (hαtiny : Real.log (1/g)/Real.log (1/τ)≤(η/10)/(4*(1+η/10)))
    (hαinter : Real.log (1/g)/Real.log (1/τ)≤η/(40*(1+η)))
    (hρbudget : ρ*Real.log (k:ℝ)≤decayBudget η (η/8)/4) :
    ∃C:ℝ,0<C ∧ ∃N0:ℕ,2≤N0 ∧ ∀N:ℕ,N0≤N → ∀L:ℕ,
      ∀cuts:Cuts k N (L+1),∀hN:0<N,
      ((L+1:ℕ):ℝ)≤T*Real.log (N:ℝ) → GoodColumn (cuts.profile hN 0) g →
      EmpiricalNegativeMargin N 0 cuts hN (2*η) → integerWindowGood N cuts hN ρ γ g →
      ∀p:Fin k,∀d:Direction,∀ω:Sample cuts,∀j:Fin (pileSize cuts p),
      positiveHistory cuts p d (j.val+1) ω →
      historyGood cuts D g (η/10) (Real.sqrt (badBound N (η/10) A cH)) p d (j.val+1) ω →
      historySelfIntersection cuts D g p d (j.val+1) ω≤C*(N:ℝ)^(-decayBudget η (η/8)/2) := by
  have hk1 : 1≤k := by omega
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk1
  have hg1 : g<1 := hgK.trans_le ((div_le_one (by positivity : (0:ℝ)<k)).mpr hkr)
  have ha := decayBudget_pos hη (by positivity : 0<η/8)
  have hab := decayBudget_bounds η (η/8)
  have hgap : η/10<η-ρ*Real.log (k:ℝ) := by linarith [hab.1]
  obtain ⟨Ccur,hCcur,Nc,hNc,hcur⟩ := currentRunBound k D (by omega) hD g τ T η hg hg1 hτ hτg hT hη hα hαinter
  obtain ⟨Csum,hCsum,Nb,hNb,hblock⟩ := regimeBlockAverage_uniform k D hk hD T η g τ hT hη hg hgK hτ hτg hα hαtiny hαinter
  obtain ⟨Nf,hNf,hfamily⟩ := preparedFamily_exists k hk1 η ρ (η/10) γ hρ hγ hγ1 hgap
  obtain ⟨C,hC,Ns,hNs,hscale⟩ := conditionalScale (decayBudget η (η/8)) (η/10) A cH Ccur Csum
    (2*(k:ℝ)^3*T) ha (by positivity) hcH hCcur.le hCsum.le (by positivity)
  refine ⟨C,hC,Nc+Nb+Nf+Ns,by omega,?_⟩
  intro N hNN L cuts hN hL hfirst hmargin hwindow p d ω j hpos hhistory
  have hN2 : 2≤N := by omega
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hβ : empiricalBeta N 0 cuts hN (L+1)≤-η := by
    have hh := hmargin.1
    simp only [zero_add] at hh
    linarith
  by_cases hdir : hasDirection cuts D g d (revealWords cuts p d ω j)
  · obtain ⟨B,hcard,hcover,hdepth,hsep,hprepared⟩ := hfamily N (by omega) L T hL cuts hN g hwindow hβ
      p d (revealWords cuts p d ω j) (revealWords_first cuts p d ω j)
    let x : B → Prefix k (L+1) := fun a => a.val
    have hsep' : ∀a b:B,a≠b → prefixSeparated (x a) (x b) := by
      intro a b hab
      exact hsep a.val a.property b.val b.property (fun he => hab (Subtype.ext he))
    have hfuture : ∀a:B,∀w,inCylinder (x a) w → strictFuture d (revealWords cuts p d ω j) w := by
      intro a w hw
      exact ((hcover w).mpr ⟨a.val,a.property,hw⟩).2
    have hcover' : ∀w:Word k (L+1),w.get 0=p → strictFuture d (revealWords cuts p d ω j) w → ∃a:B,inCylinder (x a) w := by
      intro w hp hw
      obtain ⟨a,ha,haw⟩ := (hcover w).mp ⟨hp,hw⟩
      exact ⟨⟨a,ha⟩,haw⟩
    have hblocks (a:B) : historyBlockAverage cuts p d j x a ω≤
        Csum*(N:ℝ)^(-decayBudget η (η/8))+2*(N:ℝ)^2*Real.sqrt (badBound N (η/10) A cH) := by
      apply hblock N (by omega) L cuts hN hL hfirst hmargin _ (Real.sqrt_nonneg _) p d ω j hpos hhistory hdir B x hsep' a
        (hdepth a.val a.property) (fun w hw => ((hcover w).mpr ⟨a.val,a.property,hw⟩).1) (hfuture a)
      rcases hprepared a.val a.property with ht | hg
      · exact Or.inl ht
      · obtain ⟨c,b,e,hc,_,_,_,hgc,_,_⟩ := hg
        exact Or.inr ⟨c,by simpa using hc,hgc⟩
    have hcurrent := hcur N (by omega) L hL cuts hN hfirst hβ (η/10) _ (Real.sqrt_nonneg _) p d ω j hpos hhistory hdir
    have hcurrent' : conditionalExpect (fixedCountPMF cuts) (currentExcess cuts p d j ω)
        (historyFiber cuts p d (j.val+1) ω)≤Ccur*(N:ℝ)^(-decayBudget η (η/8))+
          N*Real.sqrt (badBound N (η/10) A cH) := by
      apply hcurrent.trans
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNr (by linarith [hab.2.1])) hCcur.le
    have hs := Finset.sum_le_sum (fun a (_:a∈(Finset.univ:Finset B)) => hblocks a)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at hs
    have hh := (historySelfIntersection_family cuts D g p d ω j x hpos hsep' hfuture hcover').trans
      (add_le_add hcurrent' hs)
    have hbound : historySelfIntersection cuts D g p d (j.val+1) ω≤
        (Ccur+(B.card:ℝ)*Csum)*(N:ℝ)^(-decayBudget η (η/8))+
        ((N:ℝ)+2*(B.card:ℝ)*(N:ℝ)^2)*Real.sqrt (badBound N (η/10) A cH) := by
      apply hh.trans_eq
      ring
    exact hbound.trans (hscale N (by omega) B.card (ρ*Real.log (k:ℝ)) (Nat.cast_nonneg _)
      (mul_nonneg hρ.le (Real.log_nonneg hkr)) hρbudget hcard)
  · rw [historySelfIntersection_zero_of_not_direction cuts D g p d ω j hdir]
    positivity

end RiffleUpperV2.Conditional
