import RiffleLowerV2.Localization.Geometry.Algebra
import RiffleLowerV2.Localization.Geometry.Empirical

noncomputable section
open TimeProfile Set
namespace RiffleLowerV2.Localization

/-- Specialize finite error algebra to the actual empirical witness and selected classes. -/
theorem geometry_exponent_bounds {k N K : ℕ} (hk : 2 ≤ k) (hN2 : 2 ≤ N)
    (cuts : Cuts k N K) (hN : 0 < N) {eta rho chi : ℝ}
    (heta : 0 < eta) (hrho : 0 < rho) (P : BorelPartition k)
    (W : ColdWitnessData) (G : ColdGeometryData K P W)
    (hW : WitnessSpec cuts hN eta rho chi W)
    (hpa : TypeApproximation cuts hN P (prefixColumns K W) W.theta (geometryError eta) G.prefixType)
    (hta : TypeApproximation cuts hN P (tailColumns K W) 2 (geometryError eta) G.tailType)
    (hbr : BridgeSpec cuts hN rho chi G)
    (hdel : (2*rho+1/logScale N)*Real.log k ≤ kappa0 eta/50)
    (hbrcost : 2*rho*Real.log k+(Real.log k+2*Real.log (1/chi))/logScale N ≤ kappa0 eta/50) :
    let b := beta cuts hN (W.s N)
    let ellp := geometryEllP cuts hN P W G
    let hp := typeH cuts hN P (prefixColumns K W) G.prefixType
    let h := geometryH cuts hN P W G
    let z := geometryZ cuts hN P W G
    let g := geometryG cuts hN P W G
    b/2+2*kappa eta ≤ ellp ∧ hp ≤ ellp-kappa eta ∧ kappa eta/2 ≤ h ∧
      kappa eta/2 ≤ g-h/2 ∧ z ≤ 2*kappa0 eta := by
  dsimp only
  have hkap : 0 < kappa eta := by unfold kappa; positivity
  have hkap0 : 0 < kappa0 eta := by unfold kappa0; positivity
  dsimp only [WitnessSpec] at hW
  rcases hW with ⟨hbl, hms, hdepth, htheta, _, _, hj, _, hh, _, hgap, hmean, hterm⟩
  have htheta2 : W.theta ∈ Icc (2 : ℝ) 4 := ⟨by linarith [htheta.1], htheta.2⟩
  have hhh := (Witness.H_bounds Witness.oneColumnTilt hk hN2 cuts hN htheta2
    (gridTime_mono hN2 hms)).2
  have hpa' := typeApproximation_grid hN2 cuts hN P hms W.theta (geometryError eta) G.prefixType hpa
  have hta' := typeApproximation_grid hN2 cuts hN P hdepth 2 (geometryError eta) G.tailType hta
  change |typeJ N G.tailType - J cuts hN 2 (gridTime N (W.mu+W.bridgeLength)) (horizon N K)| +
    |typeH cuts hN P (tailColumns K W) G.tailType -
      H cuts hN 2 (gridTime N (W.mu+W.bridgeLength)) (horizon N K)| ≤ geometryError eta at hta'
  have hsub := tail_grid_cost_sub cuts hN W.mu W.bridgeLength
  rw [hsub.1, hsub.2] at hta'
  have hd := bridge_grid_cost_bounds hk hN2 cuts hN hrho hbl hdepth
  dsimp only at hd
  have hbj : J cuts hN 2 (gridTime N W.mu) (gridTime N (W.mu+W.bridgeLength)) ≤ kappa0 eta/50 :=
    hd.2.1.trans hdel
  have hbh : H cuts hN 2 (gridTime N W.mu) (gridTime N (W.mu+W.bridgeLength)) ≤ kappa0 eta/50 :=
    hd.2.2.2.trans hdel
  rcases hbr with ⟨_, _, _, _, _, _, _, _, _, _, hell0, hellraw⟩
  have hell := hellraw.trans hbrcost
  have hprefix := prefix_exponent_buffers hkap (geometryError_le_kappa eta) hhh hj hh hpa'
  have hcollision := collision_exponent_buffers hkap hkap0 (min_le_left _ _)
    (geometryError_le_kappa0 eta) hpa' hta' hd.1 hbj hbh hell0 hell hgap (hmean.trans_lt hterm)
  exact ⟨hprefix.1, hprefix.2.1, hprefix.2.2, hcollision.1, hcollision.2⟩

end RiffleLowerV2.Localization
