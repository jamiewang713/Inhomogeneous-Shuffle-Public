import RiffleLowerV2.Shared
import RiffleTimeProfile.Analysis

noncomputable section
namespace RiffleLowerV2.ProfileTransfer
open TimeProfile

/-- An explicit threshold; the final rounding error is at most one quarter of e. -/
def transferThreshold (C e : ℝ) : ℕ := max 2 ⌈Real.exp (4 * C / e)⌉₊

theorem transferThreshold_spec (C : ℝ) {e : ℝ} (he : 0 < e) :
    2 ≤ transferThreshold C e ∧
      ∀ N : ℕ, transferThreshold C e ≤ N → C / logScale N ≤ e / 4 := by
  refine ⟨le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hnc : ⌈Real.exp (4 * C / e)⌉₊ ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hexp : Real.exp (4 * C / e) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnc)
  have hlog : 4 * C / e ≤ logScale N := (Real.le_log_iff_exp_le hNpos).mpr hexp
  have hmul := (div_le_iff₀ he).mp hlog
  apply (div_le_iff₀ (logScale_pos hN2)).mpr
  nlinarith

/-- The spatial partition scale is fixed before rho, phi, or the time law. -/
def transferChi (k : ℕ) (T e : ℝ) : ℝ := min (1 / (2 * (k : ℝ))) (e / (8 * (T + 1)))

theorem transferChi_spec {k : ℕ} (hk : 2 ≤ k) {T e : ℝ} (hT : 0 < T) (he : 0 < e) :
    0 < transferChi k T e ∧ transferChi k T e < 1 / (k : ℝ) ∧
      2 * T * transferChi k T e ≤ e / 4 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hc : 0 < transferChi k T e := by unfold transferChi; positivity
  have hck := min_le_left (1 / (2 * (k : ℝ))) (e / (8 * (T + 1)))
  have hct := min_le_right (1 / (2 * (k : ℝ))) (e / (8 * (T + 1)))
  change transferChi k T e ≤ _ at hck hct
  refine ⟨hc, hck.trans_lt ?_, ?_⟩
  · apply one_div_lt_one_div_of_lt hkpos
    linarith
  · have hh := (le_div_iff₀ (show 0 < 8 * (T + 1) by positivity)).mp hct
    nlinarith

def transferRho (M e rhoCeiling : ℝ) : ℝ := min rhoCeiling (e / (16 * (M + 1)))
def transferPhi (m : ℕ) (T M e : ℝ) : ℝ := e / (4 * (M * m * T + 1))
def transferRounding (m : ℕ) (T M rho : ℝ) : ℝ := 4 * M * m * (T / rho + 2) + 6 * M

theorem transferRho_spec {M e rhoCeiling : ℝ}
    (hM : 0 ≤ M) (he : 0 < e) (hceil : 0 < rhoCeiling) :
    0 < transferRho M e rhoCeiling ∧ transferRho M e rhoCeiling ≤ rhoCeiling ∧
    ∀ rho : ℝ, 0 < rho → rho ≤ transferRho M e rhoCeiling → 4 * M * rho ≤ e / 4 := by
  refine ⟨by unfold transferRho; positivity, min_le_left _ _, ?_⟩
  intro rho hrho hr
  have hh := hr.trans (min_le_right rhoCeiling (e / (16 * (M + 1))))
  have hh' := (le_div_iff₀ (show 0 < 16 * (M + 1) by positivity)).mp hh
  nlinarith

theorem transferPhi_spec (m : ℕ) {T M e : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (he : 0 < e) :
    0 < transferPhi m T M e ∧
      ∀ phi : ℝ, 0 < phi → phi ≤ transferPhi m T M e → M * m * phi * T ≤ e / 4 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  refine ⟨by unfold transferPhi; positivity, ?_⟩
  intro phi hphi hp
  have hh := (le_div_iff₀ (show 0 < 4 * (M * m * T + 1) by positivity)).mp hp
  nlinarith

theorem transfer_error_budget {N m : ℕ} {T M e chi rho phi : ℝ}
    (he : 0 < e) (hchi : 2 * T * chi ≤ e / 4)
    (hrho : 4 * M * rho ≤ e / 4) (hphi : M * m * phi * T ≤ e / 4)
    (hN : transferThreshold (transferRounding m T M rho) e ≤ N) :
    2 * T * chi + M * m * phi * T + 4 * M * rho +
      (4 * M * m * (T / rho + 2) + 6 * M) / logScale N ≤ e := by
  have hround := (transferThreshold_spec (transferRounding m T M rho) he).2 N hN
  unfold transferRounding at hround
  linarith

end RiffleLowerV2.ProfileTransfer
