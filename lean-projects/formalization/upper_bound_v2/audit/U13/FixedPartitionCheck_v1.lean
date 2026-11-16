-- U13 independently compiled source snapshot.
-- Source SHA256: 12be78965a1c53cc41a41a02b6107f69b71504d0fcbf9cd8ef2ee6fda6a2fb43
import RiffleLowerV2.ProfileTransfer.Quadrature
import RiffleLowerV2.ProfileTransfer.Spatial
import RiffleLowerV2.ProfileTransfer.Parameters

/-!
The scalar transfer for an arbitrary fixed regular partition.  All time
integrability hypotheses refer to that same partition.  This module does
not select a partition and does not assume continuity in time.
-/

noncomputable section
open Set MeasureTheory
namespace RiffleUpperV2.Margins
open TimeProfile RiffleLowerV2 RiffleLowerV2.Targets RiffleLowerV2.ProfileTransfer

/-- The explicit common scalar error, using the checked bound `4 log k`. -/
def scalarError (k N m : ℕ) (T rho phi omega : ℝ) : ℝ :=
  2*T*omega + (4*Real.log (k : ℝ))*m*phi*T + 4*(4*Real.log (k : ℝ))*rho +
    (4*(4*Real.log (k : ℝ))*m*(T/rho+2)+6*(4*Real.log (k : ℝ)))/logScale N

/-- Quantitative transfer accepts the caller's partition with any fixed common
regularity constant. The population here is the whole deck, so its logarithmic
scale is N; later integer-grid adapters keep this explicit. -/
theorem fixedPartitionQuadrature {k N : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    {T rho phi chi C : ℝ} (hT : 0 < T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : 0 ≤ chi) (hC : 0 ≤ C)
    (P : BorelPartition k) (hP : P.IsRegular chi C)
    (μ : TimeLaw k) (hμ : ScalarIntegrable μ P T)
    (cuts : HorizonCuts k N T)
    (hLike : AlmostLike cuts (deckPos hN) μ P T rho phi) :
    ProfileIntervalErrors T cuts (deckPos hN) μ
      (scalarError k N P.cellCount T rho phi (C*chi)) := by
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hM : 0 ≤ 4*Real.log (k : ℝ) := by positivity
  constructor
  · intro r s hr hrs hs
    have hf : ∀ p : Simplex k, 0 ≤ maxCost p ∧ maxCost p ≤ 4*Real.log (k : ℝ) := by
      intro p
      obtain ⟨hp0, hp⟩ := maxCost_bounds hk p
      exact ⟨hp0, hp.trans (by linarith)⟩
    exact genericQuadrature k N hN T rho phi (C*chi) (4*Real.log (k : ℝ))
      hT hrho hphi (mul_nonneg hC hchi) hM P μ maxCost
      continuous_maxCost hf hP.maxCost_oscillation hμ.1 hμ.2.1 cuts hLike r s hr hrs hs
  · intro α hα r s hr hrs hs
    exact genericQuadrature k N hN T rho phi (C*chi) (4*Real.log (k : ℝ))
      hT hrho hphi (mul_nonneg hC hchi) hM P μ (fun p => psi p α)
      (continuous_psi hα) (fun p => psi_bounds hk p hα)
      (fun i p q hp hq => hP.psi_oscillation i p q hp hq α hα)
      hμ.1 (hμ.2.2 α hα) cuts hLike r s hr hrs hs

/-- The upper quantifier order: spatial cutoff first, then any fixed regular
partition, then a caller-supplied positive mesh ceiling, then mesh and tolerance.
The final threshold is uniform in both the time law and the cut array. -/
theorem anyFixedPartitionTransfer (k : ℕ) (hk : 2 ≤ k) (T e C : ℝ)
    (hT : 0 < T) (he : 0 < e) (hC : 0 ≤ C) :
    ∃ chi0 : ℝ, 0 < chi0 ∧
      ∀ chi : ℝ, 0 < chi → chi ≤ chi0 →
      ∀ P : BorelPartition k, P.IsRegular chi C →
      ∀ rhoCeiling : ℝ, 0 < rhoCeiling →
      ∃ rho0 : ℝ, 0 < rho0 ∧ rho0 ≤ rhoCeiling ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho0 →
      ∃ phi0 : ℝ, 0 < phi0 ∧
      ∀ phi : ℝ, 0 < phi → phi ≤ phi0 →
      ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ (N : ℕ) (hN : 2 ≤ N), N0 ≤ N →
      ∀ μ : TimeLaw k, ScalarIntegrable μ P T →
      ∀ cuts : HorizonCuts k N T,
        AlmostLike cuts (deckPos hN) μ P T rho phi →
        ProfileIntervalErrors T cuts (deckPos hN) μ e := by
  let M : ℝ := 4*Real.log (k : ℝ)
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨hchipos, _, hchiBudget⟩ := transferChi_spec hk hT he
  refine ⟨transferChi k T e / (C+1), by positivity, ?_⟩
  intro chi hchi hchiSmall P hP rhoCeiling hCeiling
  have hCchi : C*chi ≤ transferChi k T e := by
    have hh := (le_div_iff₀ (show 0 < C+1 by linarith)).mp hchiSmall
    nlinarith
  have hSpatial : 2*T*(C*chi) ≤ e/4 :=
    (mul_le_mul_of_nonneg_left hCchi (by positivity)).trans hchiBudget
  obtain ⟨hrho0, hrhoCeiling, hrhoBudget⟩ := transferRho_spec hM he hCeiling
  refine ⟨transferRho M e rhoCeiling, hrho0, hrhoCeiling, ?_⟩
  intro rho hrho hrhoSmall
  obtain ⟨hphi0, hphiBudget⟩ := transferPhi_spec P.cellCount hT hM he
  refine ⟨transferPhi P.cellCount T M e, hphi0, ?_⟩
  intro phi hphi hphiSmall
  refine ⟨transferThreshold (transferRounding P.cellCount T M rho) e,
    (transferThreshold_spec _ he).1, ?_⟩
  intro N hN hNlarge μ hμ cuts hLike
  have hBudget : scalarError k N P.cellCount T rho phi (C*chi) ≤ e :=
    transfer_error_budget he hSpatial (hrhoBudget rho hrho hrhoSmall)
      (hphiBudget phi hphi hphiSmall) hNlarge
  have hErrors := fixedPartitionQuadrature hk hN hT hrho hphi.le hchi.le hC
    P hP μ hμ cuts hLike
  exact ⟨fun r s hr hrs hs => (hErrors.1 r s hr hrs hs).trans hBudget,
    fun α hα r s hr hrs hs => (hErrors.2 α hα r s hr hrs hs).trans hBudget⟩

end RiffleUpperV2.Margins

#print axioms RiffleUpperV2.Margins.fixedPartitionQuadrature
#print axioms RiffleUpperV2.Margins.anyFixedPartitionTransfer
