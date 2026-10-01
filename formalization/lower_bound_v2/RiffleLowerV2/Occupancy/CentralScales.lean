import RiffleLowerV2.Occupancy.Scales

noncomputable section
open scoped Topology
open Filter

namespace RiffleLowerV2.Occupancy
open TimeProfile

def centralConstant (D C : ℝ) : ℝ := 4*D*(C+1)+9

theorem poissonRemainder_exp_bound (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    poissonRemainder m t ≤ (m : ℝ)*Real.exp (2*t-(m : ℝ)*Real.log 2) := by
  have hs := Real.pow_div_factorial_le_exp (2*t) (show 0 ≤ 2*t by positivity) m
  have hterm : t^m/(m.factorial : ℝ) ≤ Real.exp (2*t)/(2 : ℝ)^m := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^m)).mpr
    calc
      t^m/(m.factorial : ℝ)*(2 : ℝ)^m = (2*t)^m/(m.factorial : ℝ) := by rw [mul_pow]; ring
      _ ≤ Real.exp (2*t) := hs
  have hm : ((m-1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  calc
    poissonRemainder m t = (m-1 : ℕ)*(t^m/(m.factorial : ℝ)) := by
      unfold poissonRemainder
      ring
    _ ≤ (m : ℝ)*(Real.exp (2*t)/(2 : ℝ)^m) :=
      mul_le_mul hm hterm (by positivity) (by positivity)
    _ = _ := by rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem poissonRemainder_le_inverse {N m : ℕ} (hN : 1 ≤ N)
    (hm : (m : ℝ) ≤ N) (hbudget : 3*logScale N ≤ (m : ℝ)*Real.log 2)
    {t : ℝ} (ht : 0 ≤ t) (htB : t ≤ 2*centralBound N) :
    0 ≤ poissonRemainder m t ∧ poissonRemainder m t ≤ (N : ℝ)^(-1 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : 2*t-(m : ℝ)*Real.log 2 ≤ -(13/5 : ℝ)*logScale N := by
    dsimp [centralBound] at htB
    linarith
  have hcalc : (N : ℝ)*Real.exp (-(13/5 : ℝ)*logScale N) = (N : ℝ)^(-8/5 : ℝ) := by
    rw [Real.rpow_def_of_pos hNr]
    calc
      (N : ℝ)*Real.exp (-(13/5 : ℝ)*logScale N) =
          Real.exp (Real.log (N : ℝ))*Real.exp (-(13/5 : ℝ)*logScale N) := by rw [Real.exp_log hNr]
      _ = Real.exp (Real.log (N : ℝ)*(-8/5 : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [logScale]
        ring
  refine ⟨by unfold poissonRemainder; positivity, ?_⟩
  calc
    poissonRemainder m t ≤ (m : ℝ)*Real.exp (2*t-(m : ℝ)*Real.log 2) :=
      poissonRemainder_exp_bound m ht
    _ ≤ (N : ℝ)*Real.exp (-(13/5 : ℝ)*logScale N) := by gcongr
    _ = (N : ℝ)^(-8/5 : ℝ) := hcalc
    _ ≤ (N : ℝ)^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

theorem central_moment_term_le {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    {N : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ logScale N)
    (hcube : (logScale N)^3 ≤ (N : ℝ)^(1/50 : ℝ))
    {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hsum : μ+ν ≤ 2*centralBound N) :
    momentError D C N*(1+μ)*(1+ν)*Real.exp (μ+ν) ≤
      4*D*(C+1)*(N : ℝ)^(-7/10 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 ≤ logScale N := by linarith
  have hμL : 1+μ ≤ 2*logScale N := by dsimp [centralBound] at hsum; linarith
  have hνL : 1+ν ≤ 2*logScale N := by dsimp [centralBound] at hsum; linarith
  have hCL : C*logScale N+1 ≤ (C+1)*logScale N := by nlinarith
  have hpoly : D*(C*logScale N+1)*(1+μ)*(1+ν) ≤ 4*D*(C+1)*(logScale N)^3 := by
    calc
      _ ≤ D*((C+1)*logScale N)*(2*logScale N)*(2*logScale N) := by gcongr
      _ = _ := by ring
  have hR : (momentRadius N : ℝ) ≤ (N : ℝ)^(1/25 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have he : Real.exp (μ+ν) ≤ (N : ℝ)^(1/5 : ℝ) := by
    rw [Real.rpow_def_of_pos hNr]
    apply Real.exp_le_exp.mpr
    dsimp [centralBound, logScale] at hsum ⊢
    linarith
  have hpow : (N : ℝ)^(1/50 : ℝ)*(((N : ℝ)^(1/25 : ℝ))^2/N)*(N : ℝ)^(1/5 : ℝ) =
      (N : ℝ)^(-7/10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le, ← Real.rpow_sub_one hNr.ne',
      ← Real.rpow_add hNr, ← Real.rpow_add hNr]
    norm_num
  calc
    _ = (D*(C*logScale N+1)*(1+μ)*(1+ν))*((momentRadius N : ℝ)^2/N)*Real.exp (μ+ν) := by
      unfold momentError
      ring
    _ ≤ (4*D*(C+1)*(logScale N)^3)*(((N : ℝ)^(1/25 : ℝ))^2/N)*(N : ℝ)^(1/5 : ℝ) := by gcongr
    _ ≤ (4*D*(C+1)*(N : ℝ)^(1/50 : ℝ))*(((N : ℝ)^(1/25 : ℝ))^2/N)*(N : ℝ)^(1/5 : ℝ) := by gcongr
    _ = 4*D*(C+1)*(N : ℝ)^(-7/10 : ℝ) := by rw [← hpow]; ring

/-- Uniform bounds on the entire two- and one-variable comparison errors. -/
theorem eventual_central_error_bounds (D C : ℝ) (hD : 0 < D) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      (∀ μ ν : ℝ, 0 ≤ μ → μ ≤ centralBound N → 0 ≤ ν → ν ≤ centralBound N →
        momentError D C N*(1+μ)*(1+ν)*Real.exp (μ+ν) +
          3*(poissonRemainder (bonferroniOrder N) μ + poissonRemainder (bonferroniOrder N) ν +
            poissonRemainder (bonferroniOrder N) μ * poissonRemainder (bonferroniOrder N) ν) ≤
          centralConstant D C*(N : ℝ)^(-7/10 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 2*centralBound N →
        momentError D C N*(1+t)*Real.exp t + 3*poissonRemainder (bonferroniOrder N) t ≤
          centralConstant D C*(N : ℝ)^(-7/10 : ℝ)) := by
  obtain ⟨N0,hN0⟩ := eventual_central_scales D C hD hC
  refine ⟨N0, ?_⟩
  intro N hN
  obtain ⟨hN2,hL,hm2,heven,hmR,hR,hmlow,hmN,hbudget,hcube,he0,he1⟩ := hN0 N hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hB : 0 ≤ centralBound N := by unfold centralBound; linarith
  have hinv : (N : ℝ)^(-1 : ℝ) ≤ (N : ℝ)^(-7/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
  have hinv1 : (N : ℝ)^(-1 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hNr (show (-1 : ℝ) ≤ 0 by norm_num)
  constructor
  · intro μ ν hμ hμB hν hνB
    have hmom := central_moment_term_le hD.le hC.le hN1 hL hcube hμ hν (by linarith)
    obtain ⟨hrμ0,hrμ⟩ := poissonRemainder_le_inverse hN1 hmN hbudget hμ (by linarith)
    obtain ⟨hrν0,hrν⟩ := poissonRemainder_le_inverse hN1 hmN hbudget hν (by linarith)
    have hrprod : poissonRemainder (bonferroniOrder N) μ * poissonRemainder (bonferroniOrder N) ν ≤
        (N : ℝ)^(-1 : ℝ) := by
      calc
        _ ≤ (N : ℝ)^(-1 : ℝ)*1 := mul_le_mul hrμ (hrν.trans hinv1) hrν0 (by positivity)
        _ = _ := mul_one _
    dsimp [centralConstant]
    nlinarith
  · intro t ht htB
    have hmom := central_moment_term_le hD.le hC.le hN1 hL hcube ht (show (0 : ℝ) ≤ 0 by rfl) (by simpa using htB)
    obtain ⟨hr0,hr⟩ := poissonRemainder_le_inverse hN1 hmN hbudget ht htB
    simp only [add_zero, mul_one] at hmom
    have hp : 0 ≤ (N : ℝ)^(-7/10 : ℝ) := Real.rpow_nonneg (by positivity) _
    dsimp [centralConstant]
    nlinarith

end RiffleLowerV2.Occupancy
