import RiffleLowerV2.Localization.EventBounds
import RiffleLowerV2.Localization.RankBarriers
import RiffleLowerV2.Localization.Edges
import RiffleLowerV2.Localization.Probability

noncomputable section
namespace RiffleLowerV2.Localization
open TimeProfile

/-- The single prefix event localizes the entire cold family, including every tail. -/
theorem coldLocalization_of_prefix_event {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hN2 : 2 ≤ N) {T eta rho chi xi : ℝ} (hT : 0 < T) (heta : 0 < eta)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W)
    (hW : WitnessSpec cuts hN eta rho chi W)
    (hG : GeometrySpec cuts hN eta rho chi xi P W G)
    (hK : (K : ℝ) ≤ T*logScale N)
    (hsmall : 4*(k : ℝ)*T*logScale N+4 ≤ (N : ℝ)^(kappa eta/4))
    (hlarge1 : 4 ≤ (N : ℝ)^(kappa eta/2))
    (hlarge2 : 16 ≤ (N : ℝ)^(5*kappa eta/2))
    (omega : Sample cuts) (hevent : allPrefixEvent (kappa eta/4) omega) :
    ColdLocalization hN P W G omega := by
  obtain ⟨hend, hreserve⟩ := prefix_event_cold_bounds cuts hN hN2 hT heta P W G
    hW hG hK hsmall hlarge1 hlarge2 omega hevent
  have hbridge := hG.2.2.2.2.2.2.1
  rcases hbridge with ⟨_, _, _, _, _, hminus, hplus, _⟩
  have hloc := coldFamily_localized_of_endpoint_reserves cuts hN G hW.2.1 hW.2.2.1
    hminus hplus (endpointError N k K (kappa eta) (beta cuts hN (W.s N))) omega
    (by
      intro x hx
      have he := hend x hx
      exact ⟨by linarith [abs_nonneg ((relativeUpperCount G.ambient W.ms W.mu x omega : ℝ)-
        prefixMean cuts (prefixAt W.ms G.ambient)*(relativeMassBefore cuts x+massOn cuts x))],
        by linarith [abs_nonneg ((relativeLowerCount G.ambient W.ms W.mu x omega : ℝ)-
        prefixMean cuts (prefixAt W.ms G.ambient)*relativeMassBefore cuts x)], hreserve x hx⟩)
  exact ⟨hloc, localized_collisions_supply_edges omega _ _ hloc⟩

/-- Explicit finite union bound, inherited from the actual all-prefix concentration event. -/
theorem coldLocalization_failure_le_prefixFailure {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (hN2 : 2 ≤ N) {T eta rho chi xi : ℝ} (hT : 0 < T) (heta : 0 < eta)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W)
    (hW : WitnessSpec cuts hN eta rho chi W)
    (hG : GeometrySpec cuts hN eta rho chi xi P W G)
    (hK : (K : ℝ) ≤ T*logScale N)
    (hsmall : 4*(k : ℝ)*T*logScale N+4 ≤ (N : ℝ)^(kappa eta/4))
    (hlarge1 : 4 ≤ (N : ℝ)^(kappa eta/2))
    (hlarge2 : 16 ≤ (N : ℝ)^(5*kappa eta/2)) :
    probability (fixedCountPMF cuts) (fun omega => ¬ColdLocalization hN P W G omega) ≤
      prefixFailure N k K (kappa eta/4) := by
  have hkap : 0 < kappa eta/4 := by unfold kappa; positivity
  apply le_trans _ (Thinning.allPrefixConcentration cuts hN2 _ hkap)
  apply Thinning.probability_mono
  intro omega hfail hevent
  exact hfail (coldLocalization_of_prefix_event cuts hN hN2 hT heta P W G hW hG hK
    hsmall hlarge1 hlarge2 omega hevent)

/-- The union cost is polynomial at logarithmic depth, uniformly over cuts and witnesses. -/
theorem coldLocalization_failure_le_envelope {k N K : ℕ} (hk : 2 ≤ k)
    (cuts : Cuts k N K) (hN : 0 < N) (hN2 : 2 ≤ N)
    {T eta rho chi xi : ℝ} (hT : 0 < T) (heta : 0 < eta)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W)
    (hW : WitnessSpec cuts hN eta rho chi W)
    (hG : GeometrySpec cuts hN eta rho chi xi P W G)
    (hK : (K : ℝ) ≤ T*logScale N)
    (hsmall : 4*(k : ℝ)*T*logScale N+4 ≤ (N : ℝ)^(kappa eta/4))
    (hlarge1 : 4 ≤ (N : ℝ)^(kappa eta/2))
    (hlarge2 : 16 ≤ (N : ℝ)^(5*kappa eta/2)) :
    probability (fixedCountPMF cuts) (fun omega => ¬ColdLocalization hN P W G omega) ≤
      2*(T+1)*(N : ℝ)^(1+T*Real.log k)*Real.exp (-(N : ℝ)^(kappa eta/4)/8) :=
  (coldLocalization_failure_le_prefixFailure cuts hN hN2 hT heta P W G hW hG hK
    hsmall hlarge1 hlarge2).trans (Thinning.prefixFailure_le_envelope hN2 hk hT hK _)

/-- Uniform high-probability localization with the exact fixed-count sampling law. -/
theorem localization : Targets.LocalizationTarget := by
  intro k hk T eta rho chi xi hT heta _hrho _hchi _hxi P epsilon hepsilon
  have hkap : 0 < kappa eta := by unfold kappa; positivity
  obtain ⟨Ns, hNs, hs⟩ := exists_localization_thresholds k T (kappa eta) hkap
  obtain ⟨Np, hp⟩ := Thinning.prefixFailureUniform k hk T (kappa eta/4) epsilon
    hT (by positivity) hepsilon
  refine ⟨max Ns Np, hNs.trans (le_max_left _ _), ?_⟩
  intro N hlarge cuts hN W G hW hG
  have hNsN : Ns ≤ N := (le_max_left _ _).trans hlarge
  have hNpN : Np ≤ N := (le_max_right _ _).trans hlarge
  have hN2 := hNs.trans hNsN
  have hK : (horizonDepth N T : ℝ) ≤ T*logScale N :=
    Nat.floor_le (mul_nonneg hT.le (logScale_pos hN2).le)
  obtain ⟨hsmall, hlarge1, hlarge2⟩ := hs N hNsN
  have hfailure := coldLocalization_failure_le_prefixFailure cuts hN hN2 hT heta P W G
    hW hG hK hsmall hlarge1 hlarge2
  have hprob := probability_add_complement (fixedCountPMF cuts) (ColdLocalization hN P W G)
  have hbound := hp N hNpN (horizonDepth N T) hK
  linarith

end RiffleLowerV2.Localization
