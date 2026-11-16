import RiffleLowerV2.Localization.Endpoints
import RiffleLowerV2.Localization.Concentration

noncomputable section
namespace RiffleLowerV2.Localization
open TimeProfile

/-- One actual prefix event controls both endpoint deviations and every reserve count. -/
theorem prefix_event_cold_bounds {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hN2 : 2 ≤ N) {T eta rho chi xi : ℝ} (hT : 0 < T) (heta : 0 < eta)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W)
    (hW : WitnessSpec cuts hN eta rho chi W)
    (hG : GeometrySpec cuts hN eta rho chi xi P W G)
    (hK : (K : ℝ) ≤ T*logScale N)
    (hsmall : 4*(k : ℝ)*T*logScale N+4 ≤ (N : ℝ)^(kappa eta/4))
    (hlarge1 : 4 ≤ (N : ℝ)^(kappa eta/2))
    (hlarge2 : 16 ≤ (N : ℝ)^(5*kappa eta/2))
    (omega : Sample cuts) (hevent : allPrefixEvent (kappa eta/4) omega) :
    let b := beta cuts hN (W.s N)
    let e := endpointError N k K (kappa eta) b
    (∀ x ∈ coldPrefixFamily cuts hN P W G,
      |(relativeLowerCount G.ambient W.ms W.mu x omega : ℝ) -
        prefixMean cuts (prefixAt W.ms G.ambient)*relativeMassBefore cuts x| +
      |(relativeUpperCount G.ambient W.ms W.mu x omega : ℝ) -
        prefixMean cuts (prefixAt W.ms G.ambient)*(relativeMassBefore cuts x+massOn cuts x)| ≤ e) ∧
    (∀ x ∈ coldPrefixFamily cuts hN P W G,
      e+2 ≤ (prefixCount (reservePrefix G x G.reserveMinus) omega : ℝ) ∧
      e+2 ≤ (prefixCount (reservePrefix G x G.reservePlus) omega : ℝ)) := by
  rcases hG with ⟨_, hmean, hp, _, _, _, _, hell, _, _, _, _, _, _, _, _, _, _, _, hreserve, _⟩
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, hJ, _⟩
  have hkap : 0 < kappa eta := by unfold kappa; positivity
  have hb : 4*kappa eta ≤ beta cuts hN (W.s N) := ambient_exponent_lower hJ hell
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have he := endpointError_le hN2 hT hkap hb hK hsmall
  have hms : W.ms ≤ W.mu := hW.2.1
  have hmuK : W.mu ≤ K := by have := hW.2.2.1; omega
  have hsqrt : Real.sqrt ((N : ℝ)^(beta cuts hN (W.s N))) =
      (N : ℝ)^(beta cuts hN (W.s N)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]
    congr 1
    ring
  constructor
  · intro x _
    have h := (relativeEndpoint k N K cuts G.ambient W.ms W.mu hms hmuK x omega).2.2
      ((N : ℝ)^(kappa eta/4)) (Real.rpow_pos_of_pos hNp _) hevent
    rw [hmean, hsqrt] at h
    simpa only [endpointError, hmean, prefixColumns, mul_assoc] using h
  · intro x hx
    exact ⟨reserve_count_dominates cuts hN2 hkap hb he hlarge1 hlarge2 _ (hreserve x hx).1 omega hevent,
      reserve_count_dominates cuts hN2 hkap hb he hlarge1 hlarge2 _ (hreserve x hx).2 omega hevent⟩

end RiffleLowerV2.Localization
