import RiffleLowerV2.MacroscopicLower.Parameters
import RiffleLowerV2.ProfileTransfer.Main
import RiffleLowerV2.EmpiricalLower.Main

noncomputable section
namespace RiffleLowerV2.MacroscopicLower
open TimeProfile Targets Filter
open scoped Topology

/-- The uniform macroscopic endpoint under the explicit scalar regularity of
the selected partition. All four thresholds precede N and the cut array. -/
theorem macroscopicIntegrable : Targets.MacroscopicIntegrableTarget := by
  intro k hk T eta hT heta
  have he := transferAccuracy_spec heta
  have hk0 := coldMargin_scale heta
  have hceiling := bridgeCeiling_spec hk heta
  obtain ⟨chi, hchi, hchik, P, hP, rho0, hrho0, hrhoCeiling, htransfer⟩ :=
    ProfileTransfer.profileTransfer k hk T (transferAccuracy eta) (bridgeCeiling k eta)
      hT he.1 hceiling.1
  refine ⟨chi, hchi, hchik, P, hP, rho0, hrho0,
    hceiling.2 rho0 hrhoCeiling, ?_⟩
  intro rho hrho hrhoSmall
  obtain ⟨phi0, hphi0, htransferPhi⟩ := htransfer rho hrho hrhoSmall
  refine ⟨phi0, hphi0, ?_⟩
  intro phi hphi hphiSmall chiGood gamma hchiGood hgamma epsilon hepsilon μ hμ
  obtain ⟨Nt, _, htransferN⟩ := htransferPhi phi hphi hphiSmall μ hμ
  have hparams : ColdParameters k (eta / 2) chiGood gamma rho :=
    ⟨hchiGood, hgamma, hrho, hceiling.2 rho (hrhoSmall.trans hrhoCeiling)⟩
  obtain ⟨Nl, hNl, hlargest⟩ :=
    EmpiricalLower.largestOnly k hk T (kappa0 (eta / 2)) hT hk0.1 epsilon hepsilon
  obtain ⟨Nc, _, hcold⟩ :=
    EmpiricalLower.coldOnly k hk T (eta / 2) hT (by positivity)
      chiGood gamma rho hparams epsilon hepsilon
  let Nd := ProfileTransfer.transferThreshold (Real.log (k : ℝ)) (transferAccuracy eta)
  refine ⟨max Nt (max Nd (max Nl Nc)), by omega, ?_⟩
  intro N hN hlarge cuts hLike hGood hmargin
  have hNt : Nt ≤ N := by omega
  have hNd : Nd ≤ N := by omega
  have hNlN : Nl ≤ N := by omega
  have hNc : Nc ≤ N := by omega
  by_cases hbranch : kappa0 (eta / 2) ≤
      beta cuts (deckPos hN) (horizon N (horizonDepth N T))
  · exact hlargest N hN hNlN cuts hbranch
  · have hsmall := lt_of_not_ge hbranch
    obtain ⟨_, herrors⟩ := htransferN N hN hNt cuts hLike
    have htail :=
      (ProfileTransfer.transferThreshold_spec (Real.log (k : ℝ)) he.1).2 N hNd
    have hcoldMargin := small_beta_forces_cold heta htail
      herrors.1 (by simpa only [mul_div_assoc] using herrors.2) hsmall hmargin
    exact hcold N hN hNc cuts hGood hcoldMargin.2 hsmall

/-- A sequence corollary of the uniform endpoint. Eventual admissibility permits
arbitrary initial arrays and arbitrary alternation between the two branches. -/
theorem macroscopicIntegrable_tendsto :
    ∀ (k : ℕ), 2 ≤ k → ∀ (T eta : ℝ), 0 < T → 0 < eta →
    ∃ (chiPartition : ℝ), 0 < chiPartition ∧ chiPartition < 1 / (k : ℝ) ∧
    ∃ (P : BorelPartition k), P.IsRegular chiPartition 1 ∧
    ∃ (rho0 : ℝ), 0 < rho0 ∧
        2 * rho0 * Real.log (k : ℝ) ≤ kappa0 (eta / 2) / 100 ∧
      ∀ (rho : ℝ), 0 < rho → rho ≤ rho0 →
      ∃ (phi0 : ℝ), 0 < phi0 ∧
        ∀ (phi : ℝ), 0 < phi → phi ≤ phi0 →
        ∀ (chiGood gamma : ℝ), 0 < chiGood → 0 < gamma →
        ∀ (μ : TimeLaw k), ScalarIntegrable μ P T →
        ∀ (cuts : ∀ N : ℕ, HorizonCuts k N T),
          (∀ᶠ N in atTop, ∀ hN : 2 ≤ N,
            AlmostLike (cuts N) (deckPos hN) μ P T rho phi ∧
            LocalGood (cuts N) (deckPos hN) chiGood gamma rho 0 T) →
          eta ≤ max (macroBeta μ T) (macroLambda1 μ T) →
          Tendsto (fun N => tv (physicalInverseLaw (cuts N)) (uniformPermutation N))
            atTop (𝓝 1) := by
  intro k hk T eta hT heta
  obtain ⟨chi, hchi, hchik, P, hP, rho0, hrho0, hbridge, hmacro⟩ :=
    macroscopicIntegrable k hk T eta hT heta
  refine ⟨chi, hchi, hchik, P, hP, rho0, hrho0, hbridge, ?_⟩
  intro rho hrho hrhoSmall
  obtain ⟨phi0, hphi0, hmacroPhi⟩ := hmacro rho hrho hrhoSmall
  refine ⟨phi0, hphi0, ?_⟩
  intro phi hphi hphiSmall chiGood gamma hchiGood hgamma μ hμ cuts hcuts hmargin
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hepsilon : 0 < (1 - a) / 2 := by linarith
    obtain ⟨N0, hN0, hbound⟩ :=
      hmacroPhi phi hphi hphiSmall chiGood gamma hchiGood hgamma
        ((1 - a) / 2) hepsilon μ hμ
    filter_upwards [eventually_ge_atTop N0, hcuts] with N hlarge hadmissible
    have hN : 2 ≤ N := hN0.trans hlarge
    have htv := hbound N hN hlarge (cuts N)
      (hadmissible hN).1 (hadmissible hN).2 hmargin
    linarith
  · intro b hb
    exact Eventually.of_forall fun N =>
      (Ascent.tv_le_one (physicalInverseLaw (cuts N)) (uniformPermutation N)).trans_lt hb

end RiffleLowerV2.MacroscopicLower
