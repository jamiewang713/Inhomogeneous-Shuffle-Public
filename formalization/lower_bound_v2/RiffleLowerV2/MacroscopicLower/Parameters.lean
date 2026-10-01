import RiffleLowerV2.Shared.Empirical

noncomputable section
namespace RiffleLowerV2.MacroscopicLower
open TimeProfile

/-- The scalar transfer accuracy is fixed before selecting the partition. -/
def transferAccuracy (eta : ℝ) : ℝ :=
  min (kappa0 (eta / 2) / 10) (eta / 100) / 2

theorem transferAccuracy_spec {eta : ℝ} (heta : 0 < eta) :
    0 < transferAccuracy eta ∧
      transferAccuracy eta < kappa0 (eta / 2) / 10 ∧
      transferAccuracy eta < eta / 100 := by
  have hk0 : 0 < kappa0 (eta / 2) := by unfold kappa0 kappa; positivity
  have hm : 0 < min (kappa0 (eta / 2) / 10) (eta / 100) := by positivity
  have hl := min_le_left (kappa0 (eta / 2) / 10) (eta / 100)
  have hr := min_le_right (kappa0 (eta / 2) / 10) (eta / 100)
  unfold transferAccuracy
  constructor
  · positivity
  constructor <;> linarith

theorem coldMargin_scale {eta : ℝ} (heta : 0 < eta) :
    0 < kappa0 (eta / 2) ∧ kappa0 (eta / 2) ≤ eta / 200000 := by
  constructor
  · unfold kappa0 kappa; positivity
  · unfold kappa0 kappa
    have h := min_le_left ((eta / 2 / 1000) / 100) (1 / 1000 : ℝ)
    linarith

/-- The extra mesh ceiling required by the empirical cold endpoint. -/
def bridgeCeiling (k : ℕ) (eta : ℝ) : ℝ :=
  (kappa0 (eta / 2) / 100) / (2 * Real.log (k : ℝ))

theorem bridgeCeiling_spec {k : ℕ} (hk : 2 ≤ k) {eta : ℝ} (heta : 0 < eta) :
    0 < bridgeCeiling k eta ∧
      ∀ rho : ℝ, rho ≤ bridgeCeiling k eta →
        2 * rho * Real.log (k : ℝ) ≤ kappa0 (eta / 2) / 100 := by
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hk0 := (coldMargin_scale heta).1
  refine ⟨by unfold bridgeCeiling; positivity, ?_⟩
  intro rho hrho
  have h := (le_div_iff₀ (show 0 < 2 * Real.log (k : ℝ) by positivity)).mp hrho
  nlinarith

/-- Numerical branch transfer, subsequently applied to the actual two margins. -/
theorem small_beta_forces_cold {eta betaFinite lambda0 lambda1 lambdaFinite d : ℝ}
    (heta : 0 < eta) (hd : d ≤ transferAccuracy eta / 4)
    (hbeta : |betaFinite - lambda0| ≤ transferAccuracy eta + d)
    (hlambda : |lambdaFinite - lambda1| ≤ (13 / 2 : ℝ) * transferAccuracy eta + 14 * d)
    (hsmall : betaFinite < kappa0 (eta / 2))
    (hmargin : eta ≤ max lambda0 lambda1) :
    lambda0 < eta ∧ eta / 2 ≤ lambdaFinite := by
  have hk0 := (coldMargin_scale heta).2
  have he := (transferAccuracy_spec heta).2.2
  have hb := (abs_le.mp hbeta).1
  have hl := (abs_le.mp hlambda).1
  have h0 : lambda0 < eta := by linarith
  have h1 : eta ≤ lambda1 := (le_max_iff.mp hmargin).resolve_left (not_le.mpr h0)
  exact ⟨h0, by linarith⟩

end RiffleLowerV2.MacroscopicLower
