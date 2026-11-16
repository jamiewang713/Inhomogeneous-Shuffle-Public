import RiffleLowerV2.Witness.Continuous
import RiffleLowerV2.Witness.Finite
import RiffleLowerV2.Witness.EmpiricalTilt

noncomputable section
namespace RiffleLowerV2.Witness
open TimeProfile

/-- The full finite empirical witness, with a threshold uniform over the cut array. -/
theorem coldWitness : Targets.ColdWitnessTarget := by
  intro k hk T eta rho chiGood density hT heta hrho _hchi hdensity hmesh
  have hkappa : 0 < kappa eta := by unfold kappa; positivity
  obtain ⟨Nr, hNr, hround⟩ := exists_logScale_threshold (Real.log k)
    (16*kappa eta/1000) (by positivity)
  obtain ⟨Ng, _hNg, hgoodCount⟩ := exists_logScale_gt (3/(density*rho))
  refine ⟨max Nr Ng, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN cuts hpos hmargin hterminal hgood
  have hNrN : Nr ≤ N := (le_max_left _ _).trans hN
  have hNgN : Ng ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNr.trans hNrN
  have herror : Real.log (k : ℝ)/logScale N ≤ kappa eta/1000 := by
    have h := hround N hNrN
    linarith
  have hcount : 3 < density*rho*logScale N := by
    have h := (div_lt_iff₀ (mul_pos hdensity hrho)).mp (hgoodCount N hNgN)
    nlinarith
  have hHorizon : horizon N (horizonDepth N T) ≤ T := by
    have h := (horizonDepth_error hN2 hT.le).1
    change 0 ≤ T - horizon N (horizonDepth N T) at h
    linarith
  obtain ⟨s, u, theta, htri, htheta, hb, hj, hjlow, hf⟩ :=
    continuousWitness hk hN2 cuts hpos heta hmargin
  exact roundWitness hk hN2 cuts hpos heta hrho hmesh herror hHorizon hcount
    hgood hterminal htri htheta hb hj hjlow hf

/-- All three frozen LB05 obligations, with no additional assumption. -/
theorem lB05 : Targets.LB05Target :=
  ⟨oneColumnTilt, empiricalTilt, coldWitness⟩

end RiffleLowerV2.Witness
