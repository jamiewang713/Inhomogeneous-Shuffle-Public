import RiffleTimeProfile.Base
import RiffleTimeProfile.Numerical
import RiffleTimeProfile.Source
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-! Explicit errors and quantified choices from analytic contract C07. -/

noncomputable section
open scoped BigOperators

namespace TimeProfile

def quadratureError (N : ℕ) (T rho phi : ℝ) (m : ℕ) (M omega : ℝ) : ℝ :=
  2 * omega * T + M * m * phi * T + 2 * M * rho +
    (omega + M + 2 * M * m) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N

def exceptionalAllowance (chi : ℝ) : ℝ :=
  1 / Real.sqrt (Real.log (1 / chi))

theorem quadratureError_nonneg {N m : ℕ} {T rho phi M omega : ℝ}
    (hN : 2 ≤ N) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hM : 0 ≤ M) (homega : 0 ≤ omega) :
    0 ≤ quadratureError N T rho phi m M omega := by
  have hL := logScale_pos hN
  unfold quadratureError
  positivity

theorem exceptionalAllowance_nonneg (chi : ℝ) : 0 ≤ exceptionalAllowance chi := by
  unfold exceptionalAllowance
  positivity

theorem exists_logScale_threshold (B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → B / logScale N ≤ epsilon / 16 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (16 * B / epsilon))
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hnN : n ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hexp : Real.exp (16 * B / epsilon) ≤ (N : ℝ) :=
    hn.le.trans (by exact_mod_cast hnN)
  have hlog : 16 * B / epsilon ≤ logScale N :=
    (Real.le_log_iff_exp_le hNpos).mpr hexp
  have hmul := (div_le_iff₀ hepsilon).mp hlog
  apply (div_le_iff₀ (logScale_pos hN2)).mpr
  nlinarith

theorem exists_small_chi {k : ℕ} (hk : 2 ≤ k) {T epsilon : ℝ}
    (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 ≤ 1 / (k : ℝ) ∧
      ∀ chi : ℝ, 0 < chi → chi < chi0 →
        chi * T ≤ epsilon / 16 ∧
        (4 * Real.log (k : ℝ)) * exceptionalAllowance chi ≤ epsilon / 4 := by
  let A : ℝ := 4 * Real.log (k : ℝ)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (by omega : 1 < k)))
  let B : ℝ := (4 * A / epsilon) ^ 2 + 1
  let chi0 : ℝ := min (1 / (k : ℝ))
    (min (epsilon / (16 * (T + 1))) (Real.exp (-B)))
  refine ⟨chi0, ?_, min_le_left _ _, ?_⟩
  · dsimp [chi0]
    exact lt_min (one_div_pos.mpr hkpos)
      (lt_min (div_pos hepsilon (by positivity)) (Real.exp_pos _))
  intro chi hchi hsmall
  have hlinear : chi < epsilon / (16 * (T + 1)) :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hexp : chi < Real.exp (-B) :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : B < Real.log (1 / chi) := by
    have h := Real.log_lt_log hchi hexp
    rw [Real.log_exp] at h
    simpa only [one_div, Real.log_inv, neg_neg] using (neg_lt_neg h)
  have hsqrt : 4 * A / epsilon ≤ Real.sqrt (Real.log (1 / chi)) := by
    apply Real.le_sqrt_of_sq_le
    dsimp [B] at hlog
    linarith
  have hsqrtpos : 0 < Real.sqrt (Real.log (1 / chi)) :=
    (div_pos (mul_pos (by norm_num) hA) hepsilon).trans_le hsqrt
  constructor
  · have hm := (lt_div_iff₀ (show 0 < 16 * (T + 1) by positivity)).mp hlinear
    have hp := mul_nonneg hchi.le (by norm_num : (0 : ℝ) ≤ 16)
    nlinarith
  · change A * (1 / Real.sqrt (Real.log (1 / chi))) ≤ epsilon / 4
    rw [mul_one_div]
    apply (div_le_iff₀ hsqrtpos).mpr
    have hm := (div_le_iff₀ hepsilon).mp hsqrt
    nlinarith

theorem exists_small_rho {M epsilon : ℝ} (hM : 0 ≤ M) (hepsilon : 0 < epsilon) :
    ∃ rho0 : ℝ, 0 < rho0 ∧ ∀ rho : ℝ, 0 < rho → rho < rho0 →
      2 * M * rho ≤ epsilon / 16 := by
  refine ⟨epsilon / (32 * (M + 1)), by positivity, ?_⟩
  intro rho hrho hsmall
  have h := (lt_div_iff₀ (show 0 < 32 * (M + 1) by positivity)).mp hsmall
  nlinarith

theorem exists_small_phi (m : ℕ) {T M epsilon : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hepsilon : 0 < epsilon) :
    ∃ phi0 : ℝ, 0 < phi0 ∧ ∀ phi : ℝ, 0 ≤ phi → phi ≤ phi0 →
      M * m * phi * T ≤ epsilon / 16 := by
  refine ⟨epsilon / (16 * (M * m * T + 1)), by positivity, ?_⟩
  intro phi hphi hsmall
  have h := (le_div_iff₀ (show 0 < 16 * (M * m * T + 1) by positivity)).mp hsmall
  nlinarith

theorem source_error_bounds {k N m : ℕ} {T chi rho phi er eb epsilon : ℝ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (hT : 0 ≤ T)
    (hchi : 0 < chi) (hchiK : chi < 1 / (k : ℝ))
    (hrho : 0 < rho) (hphi : 0 ≤ phi) (her : 0 ≤ er) (heb : 0 ≤ eb)
    (hepsilon : 0 < epsilon)
    (hchiBudget : chi * T ≤ epsilon / 16)
    (hbadBudget : (4 * Real.log (k : ℝ)) * exceptionalAllowance chi ≤ epsilon / 4)
    (hrhoBudget : 2 * (4 * Real.log (k : ℝ)) * rho ≤ epsilon / 16)
    (hphiBudget : (4 * Real.log (k : ℝ)) * m * phi * T ≤ epsilon / 16)
    (herBudget : (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4)
    (hebBudget : eb ≤ epsilon)
    (hNbudget :
      ((chi + (4 * Real.log (k : ℝ)) + 2 * (4 * Real.log (k : ℝ)) * m) *
        (⌊T / rho⌋₊ + 1 : ℕ) + (4 * Real.log (k : ℝ)) + Real.log (1 / chi)) /
          logScale N ≤ epsilon / 16) :
    let A := 4 * Real.log (k : ℝ)
    let E := quadratureError N T rho phi m A chi
    (chi * T ∈ Set.Icc (0 : ℝ) epsilon) ∧
    (chi * T + Real.log (1 / chi) / logScale N ∈ Set.Icc (0 : ℝ) epsilon) ∧
    ((eb + Real.log (1 / chi) / logScale N) / 2 ∈ Set.Icc (0 : ℝ) epsilon) ∧
    (E + A * (er + 1 / logScale N) ∈ Set.Icc (0 : ℝ) epsilon) ∧
    (E + A * exceptionalAllowance chi ∈ Set.Icc (0 : ℝ) epsilon) ∧
    (E ∈ Set.Icc (0 : ℝ) epsilon) := by
  let A := 4 * Real.log (k : ℝ)
  let E := quadratureError N T rho phi m A chi
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  have hL := logScale_pos hN
  have hkinv : 1 / (k : ℝ) ≤ 1 := by
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    exact (div_le_one (by positivity : (0 : ℝ) < k)).mpr hkr
  have hlog : 0 ≤ Real.log (1 / chi) :=
    Real.log_nonneg ((one_le_div hchi).mpr (hchiK.le.trans hkinv))
  have hterm : 0 ≤ (chi + A + 2 * A * m) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N := by
    positivity
  have hAnL : 0 ≤ A / logScale N := div_nonneg hA hL.le
  have hlogL : 0 ≤ Real.log (1 / chi) / logScale N := div_nonneg hlog hL.le
  have hseparate :
      (chi + A + 2 * A * m) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N +
        A / logScale N + Real.log (1 / chi) / logScale N ≤ epsilon / 16 := by
    simpa only [add_div] using hNbudget
  have htermBound :
      (chi + A + 2 * A * m) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N ≤ epsilon / 16 := by
    linarith
  have hAnLBound : A / logScale N ≤ epsilon / 16 := by linarith
  have hlogLBound : Real.log (1 / chi) / logScale N ≤ epsilon / 16 := by linarith
  have hE0 : 0 ≤ E := quadratureError_nonneg hN hT hrho hphi hA hchi.le
  have hEBound : E ≤ 5 * epsilon / 16 := by
    dsimp [E, quadratureError]
    change 2 * chi * T + A * m * phi * T + 2 * A * rho +
      (chi + A + 2 * A * m) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N ≤ _
    dsimp [A] at htermBound
    dsimp [A]
    nlinarith
  have hAalpha0 : 0 ≤ A * exceptionalAllowance chi :=
    mul_nonneg hA (exceptionalAllowance_nonneg chi)
  have her0 : 0 ≤ A * er := mul_nonneg hA her
  change (chi * T ∈ Set.Icc (0 : ℝ) epsilon) ∧
    (chi * T + Real.log (1 / chi) / logScale N ∈ Set.Icc (0 : ℝ) epsilon) ∧
    ((eb + Real.log (1 / chi) / logScale N) / 2 ∈ Set.Icc (0 : ℝ) epsilon) ∧
    (E + A * (er + 1 / logScale N) ∈ Set.Icc (0 : ℝ) epsilon) ∧
    (E + A * exceptionalAllowance chi ∈ Set.Icc (0 : ℝ) epsilon) ∧
    (E ∈ Set.Icc (0 : ℝ) epsilon)
  have hshift : A * (er + 1 / logScale N) = A * er + A / logScale N := by ring
  rw [hshift]
  dsimp [A] at hEBound hAalpha0 her0 hAnLBound
  dsimp [A]
  refine ⟨⟨mul_nonneg hchi.le hT, by linarith⟩,
    ⟨by positivity, by linarith⟩,
    ⟨by positivity, by linarith⟩,
    ⟨by positivity, by linarith⟩,
    ⟨by positivity, by linarith⟩,
    ⟨hE0, by linarith⟩⟩

theorem numerical_budgets_of_common_bounds
    {eL eS eF eBeta eH eE delta epsilon eta : ℝ}
    (heL : eL ∈ Set.Icc (0 : ℝ) epsilon)
    (heS : eS ∈ Set.Icc (0 : ℝ) epsilon)
    (heF : eF ∈ Set.Icc (0 : ℝ) epsilon)
    (heBeta : eBeta ∈ Set.Icc (0 : ℝ) epsilon)
    (heH : eH ∈ Set.Icc (0 : ℝ) epsilon)
    (heE : eE ∈ Set.Icc (0 : ℝ) epsilon)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) epsilon)
    (hepsilon : epsilon ≤ eta / 28) :
    largeLoss eL eF eBeta delta eH eE ≤ eta / 2 ∧
    smallLoss eBeta eF eS eH eE ≤ eta / 2 ∧
    eBeta + eE ≤ eta / 2 ∧ eBeta + 2 * eF ≤ eta := by
  have hlarge : largeLoss eL eF eBeta delta eH eE ≤ (25 : ℝ) * epsilon / 2 := by
    unfold largeLoss
    linarith [heL.2, heF.2, heBeta.2, hdelta.2, heH.2, heE.2]
  have hsmall : smallLoss eBeta eF eS eH eE ≤ (27 : ℝ) * epsilon / 2 := by
    unfold smallLoss
    linarith [heBeta.2, heF.2, heS.2, heH.2, heE.2]
  have heps : 0 ≤ epsilon := heL.1.trans heL.2
  refine ⟨by linarith, by linarith, by linarith [heBeta.2, heE.2],
    by linarith [heBeta.2, heF.2]⟩

theorem exists_source_parameter_thresholds {k : ℕ} (hk : 2 ≤ k)
    {T epsilon : ℝ} (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 ≤ 1 / (k : ℝ) ∧
      ∀ chi : ℝ, 0 < chi → chi < chi0 →
        chi * T ≤ epsilon / 16 ∧
        (4 * Real.log (k : ℝ)) * exceptionalAllowance chi ≤ epsilon / 4 ∧
        ∀ m : ℕ, ∃ rho0 : ℝ, 0 < rho0 ∧
          ∀ rho : ℝ, 0 < rho → rho < rho0 →
            2 * (4 * Real.log (k : ℝ)) * rho ≤ epsilon / 16 ∧
            ∃ phi0 : ℝ, 0 < phi0 ∧
              ∀ phi : ℝ, 0 ≤ phi → phi ≤ phi0 →
                (4 * Real.log (k : ℝ)) * m * phi * T ≤ epsilon / 16 ∧
                ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
                  ((chi + (4 * Real.log (k : ℝ)) +
                    2 * (4 * Real.log (k : ℝ)) * m) * (⌊T / rho⌋₊ + 1 : ℕ) +
                    (4 * Real.log (k : ℝ)) + Real.log (1 / chi)) /
                      logScale N ≤ epsilon / 16 := by
  have hA : 0 ≤ 4 * Real.log (k : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  obtain ⟨chi0, hchi0, hchi0k, hchiSmall⟩ := exists_small_chi hk hT hepsilon
  refine ⟨chi0, hchi0, hchi0k, ?_⟩
  intro chi hchi hsmall
  obtain ⟨hchiBudget, hbadBudget⟩ := hchiSmall chi hchi hsmall
  refine ⟨hchiBudget, hbadBudget, ?_⟩
  intro m
  obtain ⟨rho0, hrho0, hrhoSmall⟩ := exists_small_rho hA hepsilon
  refine ⟨rho0, hrho0, ?_⟩
  intro rho hrho hsmallRho
  refine ⟨hrhoSmall rho hrho hsmallRho, ?_⟩
  obtain ⟨phi0, hphi0, hphiSmall⟩ := exists_small_phi m hT hA hepsilon
  refine ⟨phi0, hphi0, ?_⟩
  intro phi hphi hsmallPhi
  refine ⟨hphiSmall phi hphi hsmallPhi, ?_⟩
  exact exists_logScale_threshold _ epsilon hepsilon

theorem uniformly_vanishing_ambient_budgets {ι : ℕ → Type*}
    (allowed : ∀ N, Set (ι N)) (er eb : ∀ N, ι N → ℝ)
    (her : UniformlyVanishing allowed er) (heb : UniformlyVanishing allowed eb)
    {A epsilon : ℝ} (hA : 0 ≤ A) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ x ∈ allowed N,
      A * |er N x| ≤ epsilon / 4 ∧ |eb N x| ≤ epsilon := by
  have htol : 0 < epsilon / (4 * (A + 1)) := by positivity
  obtain ⟨Nr, hNr⟩ := her (epsilon / (4 * (A + 1))) htol
  obtain ⟨Nb, hNb⟩ := heb epsilon hepsilon
  refine ⟨max Nr Nb, ?_⟩
  intro N hN x hx
  have hr := hNr N ((le_max_left _ _).trans hN) x hx
  have hb := hNb N ((le_max_right _ _).trans hN) x hx
  have hm := (le_div_iff₀ (show 0 < 4 * (A + 1) by positivity)).mp hr
  refine ⟨?_, hb⟩
  nlinarith [abs_nonneg (er N x)]

end TimeProfile
