import RiffleUpperV2.Contracts.V1.Profile
import RiffleUpperV2.Contracts.V1.Empirical
import RiffleUpperV2.Margins.ProfileMargin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Set Filter
namespace RiffleUpperV2.ProfileUpper
open TimeProfile

theorem powerDecay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N : ℝ)^(-c)) atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

/-- Internal composition: the public export discharges E with U11. -/
theorem bufferedOfEmpirical (hE : Contracts.V1.E) : Contracts.V1.P := by
  intro k hk T η hT hη
  obtain ⟨χ0, hχ0, hχtransfer⟩ := Margins.anyFixedPartitionTransfer k hk T (η/100)
    (regularityConstant k) hT (by positivity) (by simp [regularityConstant])
  refine ⟨χ0, hχ0, ?_⟩
  intro χ hχ hχsmall P hP g γ hg hgk hγ
  obtain ⟨ρE, hρE, hEmp⟩ := hE k hk T (η/2) g γ hT (by positivity) hg hγ
  obtain ⟨ρ0, hρ0, hρ0E, htransfer⟩ := hχtransfer χ hχ hχsmall P hP ρE hρE
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ hρ hρsmall
  obtain ⟨c, hc, NE, hNE, hEst⟩ := hEmp ρ hρ (hρsmall.trans hρ0E)
  obtain ⟨φ0, hφ0, hφtransfer⟩ := htransfer ρ hρ hρsmall
  refine ⟨φ0, hφ0, ?_⟩
  intro φ hφ hφsmall μ hμ hmargin ε hε
  obtain ⟨NS, hNS, hscalar⟩ := hφtransfer φ hφ hφsmall
  have hsmall := (powerDecay hc).eventually (eventually_lt_nhds hε)
  obtain ⟨ND, hND⟩ := eventually_atTop.mp hsmall
  let NM := RiffleLowerV2.ProfileTransfer.transferThreshold (14*Real.log (k : ℝ)) η
  refine ⟨max NE (max NS (max ND NM)), by omega, ?_⟩
  intro N hN cuts hLike hGood
  have hN2 : 2 ≤ N := by omega
  have hm := Margins.profileToEmpiricalMargin_half hk hN2 hT hη
    (show NM ≤ N by omega) P μ hμ cuts
    (hscalar N hN2 (by omega) μ hμ cuts hLike)
    ((le_max_left _ _).trans hmargin) ((le_max_right _ _).trans hmargin)
  have hKT : (horizonDepth N T : ℝ) ≤ T * Real.log (N : ℝ) :=
    Nat.floor_le (mul_nonneg hT.le (logScale_pos hN2).le)
  have hH : (horizonDepth N T : ℝ) / Real.log (N : ℝ) ≤ T :=
    (div_le_iff₀ (logScale_pos hN2)).mpr hKT
  have hg' : LocalGood cuts (by omega) g γ ρ 0
      ((horizonDepth N T : ℝ) / Real.log (N : ℝ)) :=
    fun a ha haρ => hGood a ha (haρ.trans hH)
  exact (hEst N (by omega) (horizonDepth N T) hKT cuts hm hg').trans
    (hND N (by omega)).le

end RiffleUpperV2.ProfileUpper
