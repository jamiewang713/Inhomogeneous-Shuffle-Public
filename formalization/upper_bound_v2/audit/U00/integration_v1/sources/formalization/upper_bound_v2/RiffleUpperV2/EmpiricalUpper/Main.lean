import RiffleUpperV2.EmpiricalUpper.Parameters
import RiffleUpperV2.EmpiricalUpper.Rates
import RiffleUpperV2.FirstMoment.Empirical
import RiffleUpperV2.Conditional.Main

/-! The exact empirical endpoint on the actual chronological inverse law.
Every conditional and exploration estimate is constructed in the imported
proved model chain; the only endpoint inputs are the empirical margin and
local-good condition. -/
noncomputable section
namespace RiffleUpperV2.EmpiricalUpper
open Exploration Exponential TimeProfile

/-- Source: thm:ub-empirical-upper and eq:ub-empirical-tv-conclusion. -/
theorem empiricalUpper : Contracts.V1.E := by
  have conditional : Contracts.V1.C := Conditional.remainingCommonEdges
  intro k hk T η0 g0 γ0 hT hη0 hg0 hγ0
  let η := upperEta η0
  let g := upperGood k g0
  let γ := upperDensity γ0
  obtain ⟨hη,hη1,hηbudget⟩ := upperEta_spec hη0
  obtain ⟨hg,hgg0,hgk⟩ := upperGood_spec hk hg0
  obtain ⟨hγ,hγγ0,hγ1⟩ := upperDensity_spec hγ0
  change 0 < η at hη
  change η ≤ 1 at hη1
  change 4*η ≤ η0 at hηbudget
  change 0 < g at hg
  change g ≤ g0 at hgg0
  change g < 1/(k : ℝ) at hgk
  change 0 < γ at hγ
  change γ ≤ γ0 at hγγ0
  change γ ≤ 1 at hγ1
  obtain ⟨δF,hδF,NF,hNF,hFirst⟩ := FirstMoment.empiricalFirstMoment k hk T η (g/2)
    hT hη (by positivity) (by linarith)
  let a := upperAlpha η δF
  have ha : 0 < a := upperAlpha_pos hη hδF
  obtain ⟨ρC,hρC,hconditional⟩ := conditional k hk T η g γ hT hη hη1 hg hgk hγ hγ1
  obtain ⟨ρ0,hρ0,hρ0C,hbudget⟩ := completionRho hk hη ha hρC
  refine ⟨ρ0,hρ0,?_⟩
  intro ρ hρ hρρ0
  have hklog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have hρbudget := (mul_le_mul_of_nonneg_right hρρ0 hklog.le).trans hbudget
  have hρeta : ρ*Real.log (k : ℝ) ≤ η/7 := hρbudget.trans (min_le_left _ _)
  have hρone : ρ*Real.log (k : ℝ) ≤ 1/4 :=
    hρbudget.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨A,cH,ζ,C,hA,hcH,hζ,hC,NC,hNC,hconditional⟩ :=
    hconditional ρ hρ (hρρ0.trans hρ0C)
  obtain ⟨B,hB,hηB⟩ := componentBoundExists hη
  obtain ⟨c,hc,NV,hNV,hcriterion⟩ := criterion_polynomial k B (η/10) (2*η) A cH C ζ
    (by positivity) (by linarith) hcH hC hζ
  obtain ⟨NR,hNR,hrestart⟩ := restartHypotheses k hk T η0 η g γ ρ
    hη hηbudget hρ hγ hγ1 hρeta hρone
  let N0 := max NC (max NR NV)
  have hN0 : 2 ≤ N0 := hNC.trans (le_max_left _ _)
  refine ⟨c,hc,N0,hN0,?_⟩
  intro N hN K hK cuts hmargin hlocal
  have hN2 : 2 ≤ N := hN0.trans hN
  have hNCN : NC ≤ N := (le_max_left _ _).trans hN
  have hNRN : NR ≤ N := (le_max_left NR NV).trans ((le_max_right _ _).trans hN)
  have hNVN : NV ≤ N := (le_max_right NR NV).trans ((le_max_right _ _).trans hN)
  have hlocal' := localGood_mono cuts hN2 hgg0 hγγ0 hρ.le hlocal
  have hKpos := positiveHorizon hk hN2 cuts hη0 hmargin
  cases K with
  | zero => omega
  | succ K =>
    obtain ⟨r,hlen,hm,hw,hcluster,hmean,hcontract⟩ :=
      hrestart N hNRN K hK cuts hmargin hlocal'
    obtain ⟨hH,htail,hterminal⟩ := hconditional N hNCN (K-r.val)
      hlen (restartCuts cuts r) hm hw hcluster
    obtain ⟨hsmall,hbound⟩ := hcriterion N hNVN
    have hbad : 0 < badBound N (η/10) A cH := by
      unfold badBound
      exact mul_pos (mul_pos hA (Real.rpow_pos_of_pos
        (by exact_mod_cast (show 0 < N by omega)) _)) (Real.exp_pos _)
    have htailnonneg : 0 ≤ C*(N : ℝ)^(-ζ) := by positivity
    have htv := concreteExplorationTV (restartCuts cuts r) (by omega) hN2
      (clusterSpan γ) B hB g (η/10) (2*η) 1 (badBound N (η/10) A cH)
      (C*(N : ℝ)^(-ζ)) hg hbad htailnonneg hcluster hmean
      (by nlinarith) hH htail hsmall
    exact hcontract.trans (htv.trans hbound)

end RiffleUpperV2.EmpiricalUpper
