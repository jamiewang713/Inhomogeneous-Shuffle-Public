import RiffleLowerV2.Localization.Geometry.Bounds
import RiffleLowerV2.Localization.Geometry.Rates
import RiffleLowerV2.Localization.Geometry.Consequences
import RiffleLowerV2.Localization.ColdSet

noncomputable section
open TimeProfile Set
namespace RiffleLowerV2.Localization

/-- Construct the actual selected families, bridge/reserves and integer cold set uniformly. -/
theorem deterministicColdGeometry : Targets.DeterministicColdGeometryTarget := by
  intro k hk T eta rho chi hT heta hrho hchi hbudget
  have hkap : 0 < kappa eta := by unfold kappa; positivity
  obtain ⟨xi, hxi, hxiK, P, hP, Nt, hNt, htypes⟩ :=
    exists_uniform_type_data k hk T (geometryError eta) hT (geometryError_pos heta)
  obtain ⟨Ns, hNs, hscalar⟩ := exists_geometry_scalar_thresholds k hk eta rho chi heta hchi hbudget
  refine ⟨xi, hxi, hxiK, P, hP, max Nt Ns, hNt.trans (le_max_left _ _), ?_⟩
  intro N hlarge cuts hN W hW
  have hNtN : Nt ≤ N := (le_max_left _ _).trans hlarge
  have hNsN : Ns ≤ N := (le_max_right _ _).trans hlarge
  have hN2 : 2 ≤ N := hNt.trans hNtN
  have hms : W.ms ≤ W.mu := hW.2.1
  have hK : W.mu+W.bridgeLength ≤ horizonDepth N T := hW.2.2.1
  have htheta : W.theta ∈ Icc (2 : ℝ) 4 := by
    have h := hW.2.2.2.1
    exact ⟨by linarith [h.1], h.2⟩
  obtain ⟨Dp, hp, hpa⟩ := htypes N (horizonDepth N T) hNtN cuts hN (prefixColumns _ W)
    (columnSet_size hN2 hT.le W.ms W.mu) W.theta htheta
  obtain ⟨Dt, ht, hta⟩ := htypes N (horizonDepth N T) hNtN cuts hN (tailColumns _ W)
    (columnSet_size hN2 hT.le (W.mu+W.bridgeLength) (horizonDepth N T)) 2 (by norm_num)
  obtain ⟨a, ha⟩ := Thinning.exists_canonicalMaxWord cuts hN
  obtain ⟨G, hGa, hGp, hGt, hbridge, hbridgeDigits⟩ :=
    exists_bridgeGeometry cuts hN2 hN hk hrho hchi P W a ha Dp Dt hW
  have hcanonical : IsCanonicalMaxWord cuts G.ambient := by simpa only [hGa] using ha
  have hp' : TypeDataSpec cuts hN P (prefixColumns _ W) xi W.theta G.prefixType := by
    simpa only [hGp] using hp
  have ht' : TypeDataSpec cuts hN P (tailColumns _ W) xi 2 G.tailType := by
    simpa only [hGt] using ht
  have hpa' : TypeApproximation cuts hN P (prefixColumns _ W) W.theta (geometryError eta) G.prefixType := by
    simpa only [hGp] using hpa
  have hta' : TypeApproximation cuts hN P (tailColumns _ W) 2 (geometryError eta) G.tailType := by
    simpa only [hGt] using hta
  have hmean : prefixMean cuts (prefixAt W.ms G.ambient) = (N : ℝ)^(beta cuts hN (W.s N)) :=
    canonical_prefixMean_eq_rpow_beta cuts hN2 hN G.ambient hcanonical W.ms (by omega)
  have hs := hscalar N hNsN
  have he := geometry_exponent_bounds hk hN2 cuts hN heta hrho P W G hW hpa' hta' hbridge hs.1 hs.2.1
  have hset := coldRelativeSet_estimates cuts hN hN2 P W G hkap hs.2.2.1 hmean hp' he.1 he.2.1 he.2.2.1
  have hcard := coldFullFamily_card_rpow cuts hN P W G hp' ht'
  have hcentral : 0 < massOn cuts G.central := by
    rcases hbridge with ⟨_, _, _, _, _, _, _, _, _, hmass, _, _⟩
    exact (by positivity : 0 < chi^2*(k : ℝ)^(-(W.bridgeLength : ℝ))).trans_le
      (hmass G.central (by simp))
  have hmass := coldFullFamily_mass_bounds cuts hN2 hN P W G hms hK hmean hp' ht' hcentral
  have hreserve : ∀ x ∈ coldPrefixFamily cuts hN P W G,
      (N : ℝ)^(beta cuts hN (W.s N)/2+kappa eta) ≤ prefixMean cuts (reservePrefix G x G.reserveMinus) ∧
      (N : ℝ)^(beta cuts hN (W.s N)/2+kappa eta) ≤ prefixMean cuts (reservePrefix G x G.reservePlus) := by
    intro x hx
    have hpow := hs.2.2.2 (beta cuts hN (W.s N)) (geometryEllP cuts hN P W G) he.1
    constructor
    · exact hpow.trans (reservePrefix_mean_lower cuts hk hN2 hN P W G hrho hchi hms hK hW.1
        hmean hp' hbridge x hx G.reserveMinus (by simp))
    · exact hpow.trans (reservePrefix_mean_lower cuts hk hN2 hN P W G hrho hchi hms hK hW.1
        hmean hp' hbridge x hx G.reservePlus (by simp))
  have hdigits := cold_selected_digits cuts hk hN P W G hxi hchi hcanonical hp' ht' hbridgeDigits
  refine ⟨G, ?_⟩
  exact ⟨hcanonical, hmean, hp', ht', hpa', hta', hbridge, he.1, he.2.1, he.2.2.1,
    hset.1, hset.2.1, hset.2.2.1, hset.2.2.2.1, hset.2.2.2.2,
    he.2.2.2.1, he.2.2.2.2, hcard, hmass, hreserve, hdigits.1, hdigits.2.1, hdigits.2.2⟩

end RiffleLowerV2.Localization
