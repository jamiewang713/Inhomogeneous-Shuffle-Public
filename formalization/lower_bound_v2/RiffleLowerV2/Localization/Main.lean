import RiffleLowerV2.Localization.Geometry
import RiffleLowerV2.Localization.Events
import RiffleLowerV2.Witness.Main

noncomputable section
namespace RiffleLowerV2.Localization

/-- The empirical premises construct all deterministic data and the actual probability event. -/
theorem coldGeometryFromEmpirical : Targets.ColdGeometryFromEmpiricalTarget := by
  intro k hk T eta rho chi density hT heta hrho hchi hdensity hbudget
  obtain ⟨xi, hxi, hxiK, P, hP, Ng, hNg, hgeometry⟩ :=
    deterministicColdGeometry k hk T eta rho chi hT heta hrho hchi hbudget
  refine ⟨xi, hxi, hxiK, P, hP, ?_⟩
  intro epsilon hepsilon
  have hbudget' : 2*rho*Real.log k ≤ kappa eta/100 := by
    have hk0 : kappa0 eta ≤ kappa eta/100 := min_le_left _ _
    have hkap : 0 < kappa eta := by unfold kappa; positivity
    linarith
  obtain ⟨Nw, _, hwitness⟩ := Witness.coldWitness k hk T eta rho chi density
    hT heta hrho hchi hdensity hbudget'
  obtain ⟨Nl, _, hlocalization⟩ := localization k hk T eta rho chi xi
    hT heta hrho hchi hxi P epsilon hepsilon
  refine ⟨max Ng (max Nw Nl), hNg.trans (le_max_left _ _), ?_⟩
  intro N hlarge cuts hN hmargin hcold hgood
  have hNgN : Ng ≤ N := (le_max_left _ _).trans hlarge
  have hNwN : Nw ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
  have hNlN : Nl ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hlarge
  obtain ⟨W, hW⟩ := hwitness N hNwN cuts hN hmargin hcold hgood
  obtain ⟨G, hG⟩ := hgeometry N hNgN cuts hN W hW
  exact ⟨W, G, hW, hG, hlocalization N hNlN cuts hN W G hW hG⟩

/-- All four mathematical obligations of the unchanged LB09 contract are discharged. -/
theorem lB09 : Targets.LB09Target :=
  ⟨relativeEndpoint, deterministicColdGeometry, localization, coldGeometryFromEmpirical⟩

end RiffleLowerV2.Localization
