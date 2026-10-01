import RiffleLowerV2.EmpiricalLower.Scan
import RiffleLowerV2.EmpiricalLower.ManyEdges
import RiffleLowerV2.Localization.Main

noncomputable section
namespace RiffleLowerV2.EmpiricalLower
open TimeProfile Targets

/-- Source `prop:cold-lower`: every witness, geometry, occupancy, localization,
graph-representation and scan input is supplied by a checked declaration. -/
theorem coldOnly : Targets.ColdOnlyTarget := by
  intro k hk T eta hT heta chi gamma rho hparams ε hε
  rcases hparams with ⟨hchi, hgamma, hrho, hbudget⟩
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨xi, hxi, _, P, _, hconstruct⟩ :=
    Localization.coldGeometryFromEmpirical k hk T eta rho chi gamma
      hT heta hrho hchi hgamma hbudget
  obtain ⟨Ng, hNg, hgeometry⟩ := hconstruct (ε/2) hhalf
  obtain ⟨Ne, _, hedges⟩ := manyEdges k hk T eta rho chi xi
    hT heta hrho hchi hxi P (ε/2) hhalf
  obtain ⟨Nt, _, htest⟩ := coldGeometry_scan_test k eta (ε/2) heta hhalf
  refine ⟨max Ng (max Ne Nt), hNg.trans (le_max_left _ _), ?_⟩
  intro N hN hlarge cuts hgood hmargin hcold
  have hgN : Ng ≤ N := (le_max_left _ _).trans hlarge
  have heN : Ne ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
  have htN : Nt ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hlarge
  obtain ⟨W, G, hW, hG, _⟩ :=
    hgeometry N hgN cuts (deckPos hN) hmargin hcold hgood
  have hp := hedges N heN cuts (deckPos hN) W G hW hG
  have ht := htest N htN (horizonDepth N T) cuts (deckPos hN)
    rho chi xi P W G hG
  linarith

end RiffleLowerV2.EmpiricalLower
