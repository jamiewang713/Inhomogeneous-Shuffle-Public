import RiffleLowerV2.ProfileTransfer.Quadrature
import RiffleLowerV2.ProfileTransfer.Margin
import RiffleLowerV2.ProfileTransfer.Parameters

noncomputable section
open Set MeasureTheory
namespace RiffleLowerV2.ProfileTransfer
open TimeProfile Targets

/-- The selected regular partition precedes every temporal-integrability premise.
The threshold is explicit and uniform in the time law, cuts, endpoints, and alpha. -/
theorem profileTransfer : Targets.ProfileTransferTarget := by
  intro k hk T e rhoCeiling hT he hCeiling
  let M : ℝ := 4 * Real.log (k : ℝ)
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let chi := transferChi k T e
  obtain ⟨hchi, hchik, hchiBudget⟩ := transferChi_spec hk hT he
  obtain ⟨P, hP⟩ := exists_regular_partition hk hchi hchik
  obtain ⟨hrho0, hrhoCeiling, hrhoBudget⟩ := transferRho_spec hM he hCeiling
  refine ⟨chi, hchi, hchik, P, hP, transferRho M e rhoCeiling,
    hrho0, hrhoCeiling, ?_⟩
  intro rho hrho hrhoSmall
  obtain ⟨hphi0, hphiBudget⟩ := transferPhi_spec P.cellCount hT hM he
  refine ⟨transferPhi P.cellCount T M e, hphi0, ?_⟩
  intro phi hphi hphiSmall μ hμ
  let N0 := transferThreshold (transferRounding P.cellCount T M rho) e
  refine ⟨N0, (transferThreshold_spec _ he).1, ?_⟩
  intro N hN hNlarge cuts hLike
  have hBudget : 2 * T * chi + M * P.cellCount * phi * T + 4 * M * rho +
      (4 * M * P.cellCount * (T / rho + 2) + 6 * M) / logScale N ≤ e :=
    transfer_error_budget he hchiBudget (hrhoBudget rho hrho hrhoSmall)
      (hphiBudget phi hphi hphiSmall) hNlarge
  have hAB : ProfileIntervalErrors T cuts (deckPos hN) μ e := by
    constructor
    · intro r s hr hrs hs
      have hf : ∀ p : Simplex k, 0 ≤ maxCost p ∧ maxCost p ≤ M := by
        intro p
        obtain ⟨hp0, hp⟩ := maxCost_bounds hk p
        exact ⟨hp0, hp.trans (by dsimp [M]; linarith)⟩
      have hosc : ∀ i p q, P.classify p = i → P.classify q = i →
          |maxCost p - maxCost q| ≤ chi := by
        intro i p q hp hq
        simpa only [one_mul] using hP.maxCost_oscillation i p q hp hq
      exact (genericQuadrature k N hN T rho phi chi M hT hrho hphi.le hchi.le hM
        P μ maxCost continuous_maxCost hf hosc hμ.1 hμ.2.1 cuts hLike r s hr hrs hs).trans hBudget
    · intro α hα r s hr hrs hs
      have hf : ∀ p : Simplex k, 0 ≤ psi p α ∧ psi p α ≤ M :=
        fun p => psi_bounds hk p hα
      have hosc : ∀ i p q, P.classify p = i → P.classify q = i →
          |psi p α - psi q α| ≤ chi := by
        intro i p q hp hq
        simpa only [one_mul] using hP.psi_oscillation i p q hp hq α hα
      exact (genericQuadrature k N hN T rho phi chi M hT hrho hphi.le hchi.le hM
        P μ (fun p => psi p α) (continuous_psi hα) hf hosc hμ.1 (hμ.2.2 α hα)
        cuts hLike r s hr hrs hs).trans hBudget
  exact ⟨hAB, marginTransfer k N hk hN T hT P μ hμ cuts e he.le hAB⟩

end RiffleLowerV2.ProfileTransfer
