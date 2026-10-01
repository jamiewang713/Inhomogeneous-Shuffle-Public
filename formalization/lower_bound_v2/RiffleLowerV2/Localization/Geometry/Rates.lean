import RiffleLowerV2.Types.Main
import RiffleLowerV2.Witness.Rounding
import RiffleLowerV2.Localization.Geometry.Algebra

noncomputable section
open scoped Topology
open Filter TimeProfile
namespace RiffleLowerV2.Localization

/-- A fixed positive cutoff can meet any prescribed type-approximation budget. -/
theorem exists_small_type_cutoff (k : ℕ) (hk : 2 ≤ k) (B err : ℝ) (herr : 0 < err) :
    ∃ xi : ℝ, 0 < xi ∧ xi < 1/(4*(k : ℝ)) ∧ B*xi*Real.log (1/xi) ≤ err := by
  have hlim : Tendsto (fun n : ℕ => B*(Real.log (n : ℝ)/(n : ℝ))) atTop (𝓝 0) := by
    have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul B
    simpa only [mul_zero, Function.comp_def, id_eq] using h
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds herr))
  let n := max n0 (4*k+1)
  have hn0n : n0 ≤ n := le_max_left _ _
  have hn4 : 4*k < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk4 : (0 : ℝ) < 4*(k : ℝ) := by positivity
  refine ⟨1/(n : ℝ), by positivity, ?_, ?_⟩
  · apply one_div_lt_one_div_of_lt hk4
    exact_mod_cast hn4
  · have he : (1 : ℝ)/(1/(n : ℝ)) = n := by field_simp
    rw [he]
    calc
      B*(1/(n : ℝ))*Real.log (n : ℝ) = B*(Real.log (n : ℝ)/(n : ℝ)) := by ring
      _ ≤ err := (hn0 n hn0n).le

/-- Cutoff and partition precede the threshold; arrays, positions and tilts follow it. -/
theorem exists_uniform_type_data (k : ℕ) (hk : 2 ≤ k) (T err : ℝ)
    (hT : 0 < T) (herr : 0 < err) :
    ∃ xi : ℝ, 0 < xi ∧ xi < 1/(4*(k : ℝ)) ∧
    ∃ P : BorelPartition k, P.IsRegular xi 1 ∧
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N K : ℕ, N0 ≤ N →
      ∀ (cuts : Cuts k N K) (hN : 0 < N) (I : Finset (Fin K)),
      (I.card : ℝ) ≤ T*logScale N → ∀ alpha ∈ Set.Icc (2 : ℝ) 4,
      ∃ D : RoundedTypeData P, TypeDataSpec cuts hN P I xi alpha D ∧
        TypeApproximation cuts hN P I alpha err D := by
  obtain ⟨Ctype, hCt, htypes⟩ := Types.roundedType k hk 1 (by norm_num)
  obtain ⟨xi, hxi, hxiK, hxerr⟩ := exists_small_type_cutoff k hk (Ctype*T) (err/2) (by positivity)
  obtain ⟨P, hP⟩ := Types.exists_type_partition hk hxi hxiK
  obtain ⟨Cround, hCr, Nt, hNt, hdata⟩ := htypes T xi hT hxi hxiK P.cellCount
  have hlim : Tendsto (fun N : ℕ => Cround*Types.roundingRate N) atTop (𝓝 0) := by
    simpa only [mul_zero] using Types.roundingRate_tendsto.const_mul Cround
  obtain ⟨Nr, hNr⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (show 0 < err/2 by positivity)))
  refine ⟨xi, hxi, hxiK, P, hP, max Nt Nr, hNt.trans (le_max_left _ _), ?_⟩
  intro N K hlarge cuts hN I hsize alpha ha
  obtain ⟨D, hD, hDa⟩ := hdata N K ((le_max_left _ _).trans hlarge) P rfl hP cuts hN I hsize alpha ha
  refine ⟨D, hD, le_trans hDa ?_⟩
  have hr := (hNr N ((le_max_right _ _).trans hlarge)).le
  dsimp [Types.roundingRate] at hr
  have hx : Ctype*T*xi*Real.log (1/xi) ≤ err/2 := hxerr
  calc
    Ctype*T*xi*Real.log (1/xi) + Cround*(Real.log (logScale N)+1)/logScale N =
        Ctype*T*xi*Real.log (1/xi) + Cround*((Real.log (logScale N)+1)/logScale N) := by ring
    _ ≤ err := by linarith

theorem exists_rpow_threshold (a C : ℝ) (ha : 0 < a) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → C ≤ (N : ℝ)^a := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nt, hNt⟩ := eventually_atTop.mp (hlim.eventually (eventually_ge_atTop C))
  exact ⟨max 2 Nt, le_max_left _ _, fun N hN => hNt N ((le_max_right _ _).trans hN)⟩

/-- Uniform finite thresholds absorb both the rounded bridge length and fixed good-digit cost. -/
theorem exists_geometry_scalar_thresholds (k : ℕ) (hk : 2 ≤ k) (eta rho chi : ℝ)
    (heta : 0 < eta) (hchi : 0 < chi)
    (hbudget : 2*rho*Real.log k ≤ kappa0 eta/100) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (2*rho+1/logScale N)*Real.log k ≤ kappa0 eta/50 ∧
      2*rho*Real.log k+(Real.log k+2*Real.log (1/chi))/logScale N ≤ kappa0 eta/50 ∧
      12/kappa eta ≤ logScale N ∧
      ∀ b ell : ℝ, b/2+2*kappa eta ≤ ell →
        (N : ℝ)^(b/2+kappa eta) ≤
          Real.exp (-1)*chi^2*(k : ℝ)^(-1 : ℝ)*(N : ℝ)^(ell-2*rho*Real.log k) := by
  have hkap : 0 < kappa eta := by unfold kappa; positivity
  have hkap0 : 0 < kappa0 eta := by unfold kappa0; positivity
  have hk0le : kappa0 eta ≤ kappa eta/100 := min_le_left _ _
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let B := |Real.log (k : ℝ)|+2*|Real.log (1/chi)|
  obtain ⟨Nr, hNr, hr⟩ := Witness.exists_logScale_threshold B (16*kappa0 eta/100) (by positivity)
  obtain ⟨Nl, hNl, hl⟩ := Witness.exists_logScale_gt (12/kappa eta)
  let c := Real.exp (-1)*chi^2*(k : ℝ)^(-1 : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Np, hNp, hp⟩ := exists_rpow_threshold (kappa eta/2) (1/c) (by positivity)
  refine ⟨max (max Nr Nl) Np, hNr.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N hN
  have hNrN : Nr ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNlN : Nl ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNpN : Np ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNr.trans hNrN
  have hL := logScale_pos hN2
  have hb : B/logScale N ≤ kappa0 eta/100 := by have := hr N hNrN; linarith
  have hlogB : Real.log (k : ℝ) ≤ B := by dsimp [B]; nlinarith [le_abs_self (Real.log (k : ℝ)), abs_nonneg (Real.log (1/chi))]
  have hcostB : Real.log (k : ℝ)+2*Real.log (1/chi) ≤ B := by
    dsimp [B]
    linarith [le_abs_self (Real.log (k : ℝ)), le_abs_self (Real.log (1/chi))]
  have hlog := (div_le_div_of_nonneg_right hlogB hL.le).trans hb
  have hcost := (div_le_div_of_nonneg_right hcostB hL.le).trans hb
  refine ⟨?_, by linarith, (hl N hNlN).le, ?_⟩
  · calc
      (2*rho+1/logScale N)*Real.log k = 2*rho*Real.log k+Real.log k/logScale N := by ring
      _ ≤ kappa0 eta/50 := by linarith
  · intro b ell hell
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hg : b/2+kappa eta+kappa eta/2 ≤ ell-2*rho*Real.log k := by linarith
    have hpN := hp N hNpN
    have hcp : 1 ≤ c*(N : ℝ)^(kappa eta/2) := by
      have := mul_le_mul_of_nonneg_left hpN hc.le
      simpa only [mul_one_div_cancel hc.ne'] using this
    have hpow := Real.rpow_le_rpow_of_exponent_le hN1 hg
    have hcPow := mul_le_mul_of_nonneg_left hpow hc.le
    rw [Real.rpow_add hNpos] at hcPow
    have ht : 0 ≤ (N : ℝ)^(b/2+kappa eta) := (Real.rpow_pos_of_pos hNpos _).le
    have hprod := mul_le_mul_of_nonneg_left hcp ht
    dsimp [c] at hcPow hprod
    nlinarith

end RiffleLowerV2.Localization
