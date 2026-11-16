import RiffleLowerV2.Thinning.Main
import RiffleLowerV2.Localization.Geometry.Rates

noncomputable section
open scoped Topology
open Filter TimeProfile
namespace RiffleLowerV2.Localization

def endpointError (N k K : ℕ) (kap b : ℝ) : ℝ :=
  (N : ℝ)^(kap/4)*((2*Real.sqrt ((k : ℝ)*K)+1)*(N : ℝ)^(b/2)+2*(k : ℝ)*K+1)

theorem exists_log_linear_rpow_threshold (a B C : ℝ) (ha : 0 < a) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → B*logScale N+C ≤ (N : ℝ)^a := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)^a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => C/(N : ℝ)^a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hlim : Tendsto (fun N : ℕ => (B*logScale N+C)/(N : ℝ)^a) atTop (𝓝 0) := by
    simpa [logScale, add_div, mul_div_assoc] using (hlog.const_mul B).add hc
  obtain ⟨Nt, hNt⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 2 Nt, le_max_left _ _, ?_⟩
  intro N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh := (hNt N ((le_max_right _ _).trans hN)).le
  exact (div_le_one (Real.rpow_pos_of_pos hNp a)).mp hh

theorem endpointError_le {N k K : ℕ} (hN : 2 ≤ N) {T kap b : ℝ}
    (_hT : 0 < T) (hkap : 0 < kap) (hb : 4*kap ≤ b)
    (hK : (K : ℝ) ≤ T*logScale N)
    (hsmall : 4*(k : ℝ)*T*logScale N+4 ≤ (N : ℝ)^(kap/4)) :
    endpointError N k K kap b ≤ (N : ℝ)^(b/2+kap/2) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let d := (k : ℝ)*K
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hs : Real.sqrt d ≤ d+1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [sq_nonneg d]⟩
  have hx : 1 ≤ (N : ℝ)^(b/2) := Real.one_le_rpow hN1 (by linarith)
  have hdc : d ≤ (k : ℝ)*T*logScale N := by
    have hh := mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    simpa [d, mul_assoc] using hh
  have hbracket : (2*Real.sqrt d+1)*(N : ℝ)^(b/2)+2*d+1 ≤
      (N : ℝ)^(b/2)*(N : ℝ)^(kap/4) := by
    have haux : (2*Real.sqrt d+1)*(N : ℝ)^(b/2)+2*d+1 ≤
        (N : ℝ)^(b/2)*(4*d+4) := by
      have h0 := Real.sqrt_nonneg d
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2*d+1) (sub_nonneg.mpr hx),
        mul_le_mul_of_nonneg_right hs (Real.rpow_pos_of_pos hNp (b/2)).le]
    exact haux.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hNp _).le)
  have hh := mul_le_mul_of_nonneg_left hbracket (Real.rpow_pos_of_pos hNp (kap/4)).le
  calc
    endpointError N k K kap b ≤ (N : ℝ)^(kap/4)*((N : ℝ)^(b/2)*(N : ℝ)^(kap/4)) := by
      simpa only [endpointError, d, mul_assoc] using hh
    _ = (N : ℝ)^(b/2+kap/2) := by
      rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]
      congr 1
      ring

theorem reserve_deviation_le_half {N : ℕ} (hN : 2 ≤ N) {kap b mu : ℝ}
    (hkap : 0 < kap) (hb : 4*kap ≤ b)
    (hmu : (N : ℝ)^(b/2+kap) ≤ mu)
    (hlarge : 16 ≤ (N : ℝ)^(5*kap/2)) :
    (N : ℝ)^(kap/4)*(Real.sqrt mu+1) ≤ mu/2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmu1 : 1 ≤ mu := (Real.one_le_rpow hN1 (by linarith : 0 ≤ b/2+kap)).trans hmu
  have hmu0 : 0 ≤ mu := by linarith
  have hA0 := (Real.rpow_pos_of_pos hNp (kap/4)).le
  have hA2 : ((N : ℝ)^(kap/4))^2 = (N : ℝ)^(kap/2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    congr 1
    norm_num
    ring
  have h16 : 16*((N : ℝ)^(kap/4))^2 ≤ mu := by
    rw [hA2]
    have hprod := mul_le_mul_of_nonneg_right hlarge (Real.rpow_pos_of_pos hNp (kap/2)).le
    rw [← Real.rpow_add hNp] at hprod
    have hp : (N : ℝ)^(5*kap/2+kap/2) ≤ (N : ℝ)^(b/2+kap) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    exact hprod.trans (hp.trans hmu)
  have hs0 := Real.sqrt_nonneg mu
  have hs2 := Real.sq_sqrt hmu0
  have hs1 : 1 ≤ Real.sqrt mu := by simpa using Real.sqrt_le_sqrt hmu1
  have h4 : 4*(N : ℝ)^(kap/4) ≤ Real.sqrt mu :=
    (Real.le_sqrt (by positivity) hmu0).mpr (by nlinarith)
  nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hs1)]

theorem half_reserve_mean_dominates {N : ℕ} (hN : 2 ≤ N) {kap b mu e : ℝ}
    (_hkap : 0 < kap) (hb : 4*kap ≤ b)
    (hmu : (N : ℝ)^(b/2+kap) ≤ mu)
    (he : e ≤ (N : ℝ)^(b/2+kap/2))
    (hlarge1 : 4 ≤ (N : ℝ)^(kap/2)) (hlarge2 : 16 ≤ (N : ℝ)^(5*kap/2)) :
    e+2 ≤ mu/2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 2 ≤ (N : ℝ)^(b/2+kap/2) := by
    have hmono := Real.rpow_le_rpow_of_exponent_le hN1 (show 5*kap/2 ≤ b/2+kap/2 by linarith)
    linarith
  have hmul : 4*(N : ℝ)^(b/2+kap/2) ≤ (N : ℝ)^(b/2+kap) := by
    have h := mul_le_mul_of_nonneg_left hlarge1 (Real.rpow_pos_of_pos hNp (b/2+kap/2)).le
    rw [← Real.rpow_add hNp] at h
    have he : b/2+kap/2+kap/2 = b/2+kap := by ring
    rw [he] at h
    simpa only [mul_comm] using h
  linarith

theorem reserve_count_dominates {k N K : ℕ} (cuts : Cuts k N K) (hN : 2 ≤ N)
    {kap b e : ℝ} (hkap : 0 < kap) (hb : 4*kap ≤ b)
    (he : e ≤ (N : ℝ)^(b/2+kap/2))
    (hlarge1 : 4 ≤ (N : ℝ)^(kap/2)) (hlarge2 : 16 ≤ (N : ℝ)^(5*kap/2))
    (v : Prefix k K) (hmean : (N : ℝ)^(b/2+kap) ≤ prefixMean cuts v)
    (omega : Sample cuts) (hevent : allPrefixEvent (kap/4) omega) :
    e+2 ≤ (prefixCount v omega : ℝ) := by
  have hhalf := reserve_deviation_le_half hN hkap hb hmean hlarge2
  have hdev := (abs_le.mp (hevent v)).1
  have hgap := half_reserve_mean_dominates hN hkap hb hmean he hlarge1 hlarge2
  linarith

theorem exists_localization_thresholds (k : ℕ) (T kap : ℝ) (hkap : 0 < kap) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      4*(k : ℝ)*T*logScale N+4 ≤ (N : ℝ)^(kap/4) ∧
      4 ≤ (N : ℝ)^(kap/2) ∧ 16 ≤ (N : ℝ)^(5*kap/2) := by
  obtain ⟨N1, hN1, h1⟩ := exists_log_linear_rpow_threshold (kap/4) (4*(k : ℝ)*T) 4 (by positivity)
  obtain ⟨N2, _, h2⟩ := exists_rpow_threshold (kap/2) 4 (by positivity)
  obtain ⟨N3, _, h3⟩ := exists_rpow_threshold (5*kap/2) 16 (by positivity)
  refine ⟨max N1 (max N2 N3), hN1.trans (le_max_left _ _), ?_⟩
  intro N hN
  exact ⟨h1 N ((le_max_left _ _).trans hN),
    h2 N (((le_max_left _ _).trans (le_max_right _ _)).trans hN),
    h3 N (((le_max_right _ _).trans (le_max_right _ _)).trans hN)⟩

end RiffleLowerV2.Localization
