import RiffleLowerV2.Thinning.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped Topology
open Filter
namespace RiffleLowerV2.EmpiricalLower
open TimeProfile

/-- The contiguous-run length used for a fixed positive largest-word exponent. -/
def largestRunLength (N : ℕ) (b : ℝ) : ℕ := ⌊(N : ℝ)^(b/2)⌋₊

/-- The exact uniform-permutation run error, with its natural number of starts. -/
def largestRunError (N : ℕ) (b : ℝ) : ℝ :=
  ((N-largestRunLength N b+1 : ℕ) : ℝ) / ((largestRunLength N b).factorial : ℝ)

/-- A fixed exponential lower bound for every factorial. -/
theorem two_pow_le_two_factorial (m : ℕ) : (2 : ℝ)^m ≤ 2*(m.factorial : ℝ) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    by_cases hm : m = 0
    · subst m; norm_num
    have hm1 : (2 : ℝ) ≤ (m : ℝ)+1 := by exact_mod_cast (show 2 ≤ m+1 by omega)
    have hf : (0 : ℝ) ≤ m.factorial := by positivity
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Floor loses at most half a real parameter once that parameter is at least two. -/
theorem half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) : x/2 ≤ (⌊x⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one x
  have htwo : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hf2 : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast htwo
  linarith

/-- An elementary factorial envelope; the bound holds before any shuffle is chosen. -/
theorem floor_factorial_ratio_le {N : ℕ} {x : ℝ} (hx : 2 ≤ x) :
    (N : ℝ)/(⌊x⌋₊.factorial : ℝ) ≤
      2*(N : ℝ)*Real.exp (-(Real.log 2/2)*x) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfpos : (0 : ℝ) < ⌊x⌋₊.factorial := by positivity
  have hhalf := half_le_nat_floor hx
  have hexp : Real.exp ((Real.log 2/2)*x) ≤ 2*(⌊x⌋₊.factorial : ℝ) := by
    calc
      Real.exp ((Real.log 2/2)*x) ≤ Real.exp ((⌊x⌋₊ : ℝ)*Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = (2 : ℝ)^⌊x⌋₊ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ _ := two_pow_le_two_factorial _
  have hprod := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-((Real.log 2/2)*x)))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hprod
  apply (div_le_iff₀ hfpos).mpr
  have hN : (0 : ℝ) ≤ N := by positivity
  have := mul_le_mul_of_nonneg_left hprod hN
  convert this using 1 <;> ring_nf

/-- Polynomial times a stretched exponential, with arbitrary positive coefficient. -/
theorem power_mul_stretchedExp_tendsto (a r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N : ℝ)^a * Real.exp (-c*(N : ℝ)^r)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/r) c hc).comp
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  change ((N : ℝ)^r)^(a/r) * Real.exp (-c*(N : ℝ)^r) = _
  rw [← Real.rpow_mul hNr.le]
  have he : r*(a/r) = a := by field_simp
  rw [he]

/-- The exact factorial run error vanishes for every positive power margin. -/
theorem largestRunError_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (fun N : ℕ => largestRunError N b) atTop (𝓝 0) := by
  have hr : 0 < b/2 := by positivity
  have hx := ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 : ℝ))
  have he := (power_mul_stretchedExp_tendsto 1 (b/2) (Real.log 2/2) hr
    (by positivity : 0 < Real.log 2/2)).const_mul 2
  simp only [mul_zero, Real.rpow_one] at he
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => by
    unfold largestRunError; positivity)) _ he
  filter_upwards [hx, eventually_ge_atTop (1 : ℕ)] with N hx hN
  have hm : 2 ≤ largestRunLength N b := Nat.le_floor hx
  have hstarts : N-largestRunLength N b+1 ≤ N := by omega
  calc
    largestRunError N b ≤ (N : ℝ)/((largestRunLength N b).factorial : ℝ) := by
      unfold largestRunError
      exact div_le_div_of_nonneg_right (by exact_mod_cast hstarts) (by positivity)
    _ ≤ 2*(N : ℝ)*Real.exp (-(Real.log 2/2)*(N : ℝ)^(b/2)) :=
      floor_factorial_ratio_le hx
    _ = _ := by ring

/-- The largest-word exponential failure is uniformly bounded by a vanishing function. -/
theorem largestChernoffError_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (fun N : ℕ => Real.exp (-chernoffConstant*(N : ℝ)^b)) atTop (𝓝 0) := by
  simpa only [Real.rpow_zero, one_mul] using
    power_mul_stretchedExp_tendsto 0 b chernoffConstant hb Thinning.chernoffConstant_pos

/-- The exact prescribed floor length satisfies every finite run hypothesis eventually. -/
theorem largestRunLength_eventually_admissible (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ largestRunLength N b ∧ largestRunLength N b ≤ N ∧
      (largestRunLength N b : ℝ) ≤ (N : ℝ)^b/2 := by
  have hr : 0 < b/2 := by positivity
  have hx := ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hx, eventually_ge_atTop (1 : ℕ)] with N hx hN
  change 2 ≤ (N : ℝ)^(b/2) at hx
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : (largestRunLength N b : ℝ) ≤ (N : ℝ)^(b/2) :=
    Nat.floor_le (Real.rpow_nonneg hNr.le _)
  have hpow : (N : ℝ)^(b/2) ≤ N := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (show b/2 ≤ 1 by linarith)
  have hsq : ((N : ℝ)^(b/2))^2 = (N : ℝ)^b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 1
    norm_num
  refine ⟨Nat.le_floor hx, by exact_mod_cast hm.trans hpow, ?_⟩
  nlinarith

/-- Every word mean is bounded by the population size. -/
theorem maximalMean_le_population {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) :
    maximalMean cuts hN ≤ N := by
  have hp : (∏ j : Fin K, pileMax (cuts.profile hN j)) ≤ (1 : ℝ) := by
    apply Finset.prod_le_one
    · intro j _; exact (pileMax_pos _).le
    · intro j _; exact pileMax_le_one _
  unfold maximalMean
  nlinarith [show (0 : ℝ) ≤ N by positivity]

/-- Every accuracy has one threshold for all possible word means and cut arrays. -/
theorem largestMean_uniform_scales (b epsilon : ℝ) (hb : 0 < b) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ mu : ℝ,
      (N : ℝ)^b ≤ mu → mu ≤ N →
      2 ≤ largestRunLength N b ∧ largestRunLength N b ≤ N ∧
      (largestRunLength N b : ℝ) ≤ mu/2 ∧
      Real.exp (-chernoffConstant*mu) + largestRunError N b ≤ epsilon := by
  by_cases hb1 : b ≤ 1
  · have hsum := (largestChernoffError_tendsto b hb).add (largestRunError_tendsto b hb)
    simp only [add_zero] at hsum
    have he := hsum.eventually (eventually_lt_nhds hepsilon)
    have ha := largestRunLength_eventually_admissible b hb hb1
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp (he.and ha)
    refine ⟨max N0 2, le_max_right _ _, ?_⟩
    intro N hN mu hmulow hmuhigh
    obtain ⟨herror, hm2, hmN, hmMu⟩ := hN0 N ((le_max_left _ _).trans hN)
    have hexp : Real.exp (-chernoffConstant*mu) ≤
        Real.exp (-chernoffConstant*(N : ℝ)^b) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hmulow (by linarith [Thinning.chernoffConstant_pos])
    exact ⟨hm2, hmN, hmMu.trans (by linarith), by linarith⟩
  · refine ⟨2, le_rfl, ?_⟩
    intro N hN mu hmulow hmuhigh
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hpow : (N : ℝ)^b ≤ (N : ℝ)^(1 : ℝ) := by simpa using hmulow.trans hmuhigh
    exact False.elim (hb1 ((Real.rpow_le_rpow_left_iff hN1).mp hpow))

end RiffleLowerV2.EmpiricalLower
