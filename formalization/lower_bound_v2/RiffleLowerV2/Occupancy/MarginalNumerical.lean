import RiffleLowerV2.Occupancy.Numerical
import RiffleLowerV2.Occupancy.Scales
import RiffleLowerV2.Occupancy.Poisson

noncomputable section
open scoped Topology
open Filter
namespace RiffleLowerV2.Occupancy
open TimeProfile

def poissonBase : ℝ := Real.exp (-1)/2

theorem poissonBase_pos : 0 < poissonBase := by unfold poissonBase; positivity

theorem tau_pos {N : ℕ} (hN : 0 < N) : 0 < tau N :=
  Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem tau_pow {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (tau N)^r = (N : ℝ)^((-1/100 : ℝ)*r) := by
  rw [tau, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]

theorem benchmark_lower_at_tau {N : ℕ} {μ : ℝ}
    (ht : 0 ≤ tau N) (ht1 : tau N ≤ 1) (hμ : tau N < μ) :
    poissonBase*(tau N)^2 ≤ poissonCollision μ := by
  have hmin : (tau N)^2 ≤ min (μ^2) 1 := by
    apply le_min
    · nlinarith
    · nlinarith
  exact (mul_le_mul_of_nonneg_left hmin poissonBase_pos.le).trans
    (poissonCollision_lower_min μ (ht.trans hμ.le))

/-- Explicit numerical budgets for every marginal regime. All free constants
are fixed before the threshold, and no word mean occurs in that threshold. -/
theorem eventual_marginal_budgets (D C A : ℝ) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      2 ≤ N ∧ 10 ≤ logScale N ∧ tau N ≤ 1/2 ∧
      9*D*(C*logScale N+1)/N ≤ tau N ∧
      A*(N : ℝ)^(-7/10 : ℝ) ≤ poissonBase*(tau N)^3 ∧
      2*Real.exp (-centralBound N/2) +
        (1+centralBound N)*Real.exp (-centralBound N) ≤ tau N/2 ∧
      (3 : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) := by
  have hL := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (10 : ℝ))
  have ht := eventually_negative_rpow_le (by norm_num : (-1/100 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1/2)
  have hr := eventually_log_affine_mul_rpow_le (9*D*C) (9*D) (-1) (-1/100) (by norm_num)
  have ha := eventually_const_mul_rpow_le (A/poissonBase) (-7/10) (-3/100) (by norm_num)
  have he := eventually_log_affine_mul_rpow_le (1/5) 6 (-1/20) (-1/100) (by norm_num)
  have h3 := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/5)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (3 : ℝ))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    ((eventually_ge_atTop 2).and (hL.and (ht.and (hr.and (ha.and (he.and h3))))))
  refine ⟨N0, ?_⟩
  intro N hN
  obtain ⟨hN2,hLN,htN,hrN,haN,heN,h3N⟩ := hN0 N hN
  change 10 ≤ logScale N at hLN
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hr' : 9*D*(C*logScale N+1)/N ≤ tau N := by
    rw [Real.rpow_neg_one] at hrN
    dsimp [tau]
    convert hrN using 1
    ring
  have ha' : A*(N : ℝ)^(-7/10 : ℝ) ≤ poissonBase*(tau N)^3 := by
    have hh : (A*(N : ℝ)^(-7/10 : ℝ))/poissonBase ≤ (N : ℝ)^(-3/100 : ℝ) := by
      convert haN using 1
      ring
    have hhh := (div_le_iff₀ poissonBase_pos).mp hh
    rw [tau_pow hNp]
    norm_num
    nlinarith
  have hB : 0 ≤ centralBound N := by dsimp [centralBound]; linarith
  have hexp1 : Real.exp (-centralBound N/2) = (N : ℝ)^(-1/20 : ℝ) := by
    convert exp_logScale_mul hNp (-1/20) using 1
    congr 1
    dsimp [centralBound]
    ring
  have hexp2 : Real.exp (-centralBound N) = (N : ℝ)^(-1/10 : ℝ) := by
    convert exp_logScale_mul hNp (-1/10) using 1
    congr 1
    dsimp [centralBound]
    ring
  have hexp2' : Real.exp (-centralBound N) ≤ (N : ℝ)^(-1/20 : ℝ) := by
    rw [hexp2]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have he' : 2*Real.exp (-centralBound N/2) +
      (1+centralBound N)*Real.exp (-centralBound N) ≤ tau N/2 := by
    have hh := mul_le_mul_of_nonneg_left hexp2' (by linarith : 0 ≤ 1+centralBound N)
    rw [hexp1]
    dsimp [centralBound, tau] at *
    nlinarith
  exact ⟨hN2,hLN,htN,hr',ha',he',h3N⟩

end RiffleLowerV2.Occupancy
