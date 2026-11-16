import RiffleUpperV2.Conditional.OneHistory
import RiffleUpperV2.Contracts.V1.Conditional
import RiffleUpperV2.Exploration.UniformConcentration
import RiffleUpperV2.FirstMoment.Empirical

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open Exploration TimeProfile

/-- Source conditional remaining-common-edge theorem, with its exact frozen
quantifiers and actual natural histories. All provider hypotheses are discharged. -/
theorem remainingCommonEdges : Contracts.V1.C := by
  intro k hk T η g γ hT hη hη1 hg hgK hγ hγ1
  have hk1 : 1≤k := by omega
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk1
  have hg1 : g<1 := hgK.trans_le ((div_le_one (by positivity : (0:ℝ)<k)).mpr hkr)
  have ha := decayBudget_pos hη (by positivity : 0<η/8)
  obtain ⟨τ,ρ0,hτ,hτg,hρ0,hαtiny,hαinter,hα,hρbudget⟩ := conditionalParameter_choices hk hη
    (by positivity : 0<η/8) hg hg1
  refine ⟨ρ0,hρ0,?_⟩
  intro ρ hρ hρsmall
  have hD : 1≤clusterSpan γ := by
    have hh : 0<clusterSpan γ := Nat.ceil_pos.mpr (by positivity)
    omega
  obtain ⟨A,cH,hA,hcH,NH,hNH,hH⟩ := uniformConcentration k hk1 (clusterSpan γ) T g (η/10)
    hT hg (by positivity) (by linarith)
  obtain ⟨C1,hC1,NC,hNC,hconditional⟩ := oneHistory_uniform k (clusterSpan γ) hk hD T η g γ τ ρ A cH
    hT hη hg hgK hγ hγ1 hτ hτg hρ hcH hα hαtiny hαinter (hρbudget ρ hρ hρsmall)
  obtain ⟨NF,hNF,hfirst⟩ := FirstMoment.empiricalGraphDecay k hk T η g hT hη hg hgK
  refine ⟨A,cH,decayBudget η (η/8)/2,max C1 1,hA,hcH,by positivity,
    hC1.trans_le (le_max_left _ _),NH+NC+NF+2,by omega,?_⟩
  intro N hNN L hL cuts hmargin hwindow hcluster
  have hN2 : 2≤N := by omega
  have hN0 : 0<N := by omega
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hNr0 : (0:ℝ)<N := by exact_mod_cast hN0
  have hmarginη : EmpiricalNegativeMargin N 0 cuts hN0 η := by
    constructor
    · exact hmargin.1.trans (by linarith)
    · intro s u hs hsu hu
      exact (hmargin.2 s u hs hsu hu).trans (by linarith)
  refine ⟨hH N (by omega) L hL cuts,?_,?_⟩
  · intro p d hp i hi ω hpos hgood
    by_cases hi0 : i=0
    · subst i
      apply (remaining_initial_le_firstMoment cuts (clusterSpan γ) g (η/10) p d ω).trans
      have hL' : (L:ℝ)≤T*logScale N := (show (L:ℝ)≤(L+1:ℕ) by exact_mod_cast Nat.le_succ L).trans hL
      have hf := hfirst N N L (by omega) hN0 le_rfl cuts 0 hL' ⟨by omega,hcluster.1⟩ hmarginη
      apply hf.trans
      have hpow : (N:ℝ)^(-η/8)≤(N:ℝ)^(-(decayBudget η (η/8)/2)) := by
        apply Real.rpow_le_rpow_of_exponent_le hNr
        have hb := (decayBudget_bounds η (η/8)).2.2
        linarith
      exact hpow.trans ((le_mul_iff_one_le_left (Real.rpow_pos_of_pos hNr0 _)).mpr (le_max_right _ _))
    · by_cases hit : i=pileSize cuts p
      · subst i
        simp only [remaining_terminal,Nat.cast_zero]
        have hz : conditionalExpect (independentPairLaw cuts) (fun _ => (0:ℝ))
            (fun v => pairHistory cuts p d (pileSize cuts p) v=pairHistory cuts p d (pileSize cuts p) ω)=0 := by
          simp [conditionalExpect,RiffleLowerV2.conditionalExpect,RiffleLowerV2.expect]
        rw [hz]
        positivity
      · have hii : i<pileSize cuts p := lt_of_le_of_ne hi hit
        let j : Fin (pileSize cuts p) := ⟨i-1,by omega⟩
        have hj : j.val+1=i := by dsimp [j]; omega
        have hpair := (positivePairHistory_iff cuts p d i ω).mp hpos
        have hnot : ¬(i=0 ∨ pileSize cuts p ≤ i) := by omega
        have hgood' : historyGood cuts (clusterSpan γ) g (η/10) (Real.sqrt (badBound N (η/10) A cH)) p d i ω.1 ∧
            historyGood cuts (clusterSpan γ) g (η/10) (Real.sqrt (badBound N (η/10) A cH)) p d i ω.2 := by
          simpa only [pairHistoryGood,if_neg hnot] using hgood
        have h₁ := hconditional N (by omega) L cuts hN0 hL hcluster.1 hmargin hwindow p d ω.1 j
          (by simpa only [hj] using hpair.1) (by simpa only [hj] using hgood'.1)
        have h₂ := hconditional N (by omega) L cuts hN0 hL hcluster.1 hmargin hwindow p d ω.2 j
          (by simpa only [hj] using hpair.2) (by simpa only [hj] using hgood'.2)
        rw [hj] at h₁ h₂
        apply (remainingCommonEdges_le_self cuts (clusterSpan γ) g (η/10) p d i hp ω).trans
        have hh : (historySelfIntersection cuts (clusterSpan γ) g p d i ω.1+
            historySelfIntersection cuts (clusterSpan γ) g p d i ω.2)/2≤
            C1*(N:ℝ)^(-decayBudget η (η/8)/2) := by linarith
        apply hh.trans
        rw [neg_div]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hNr0.le _)
  · exact fun p d ω ω' => remaining_terminal cuts (clusterSpan γ) g (η/10) p d ω ω'

end RiffleUpperV2.Conditional
