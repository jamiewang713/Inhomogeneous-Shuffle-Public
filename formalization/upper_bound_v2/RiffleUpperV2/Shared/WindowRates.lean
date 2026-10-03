import RiffleUpperV2.Compat.FixedPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace RiffleUpperV2

/-- A stretched exponential with a larger exponent absorbs every fixed
real-power multiplier, with a threshold independent of all model data. -/
theorem powerExp_eventually_le {a b c : ℝ} (ha : 0 < a) (hab : b < a)
    (hc : 0 < c) (s : ℝ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (N : ℝ)^s * Real.exp (-c*(N : ℝ)^a) ≤ Real.exp (-(N : ℝ)^b) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)^a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^b/(N : ℝ)^a) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    dsimp only [Function.comp_apply]
    rw [← Real.rpow_sub hN0]
    congr 1
    ring
  have ht : Tendsto (fun N : ℕ =>
      (s*Real.log (N : ℝ)+(N : ℝ)^b)/(N : ℝ)^a) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using (hlog.const_mul s).add hpow
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually_le_const hc)
  refine ⟨max M 2,le_max_right _ _,?_⟩
  intro N hN
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmajor := (div_le_iff₀ (Real.rpow_pos_of_pos hN0 a)).mp
    (hM N ((le_max_left _ _).trans hN))
  rw [Real.rpow_def_of_pos hN0 s, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The finite smaller-side endpoint bound at w=N^(F+δ/4) has the source
stretched-exponential rate. N0 precedes both the horizon and F. -/
theorem endpointWindow_rate (T χ δ : ℝ) (hT : 0 ≤ T) (hχ : 0 < χ) (hδ : 0 < δ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N d : ℕ, N0 ≤ N →
      (d : ℝ) ≤ T*Real.log (N : ℝ) → ∀ F : ℝ, δ/2 ≤ F →
      2*((d : ℝ)+1)*Real.exp
        (-((N : ℝ)^(F+δ/4))^2 /
          (4*((d : ℝ)+1)^2*(χ⁻¹*(N : ℝ)^(2*F)+(N : ℝ)^(F+δ/4)))) ≤
        Real.exp (-(N : ℝ)^(δ/8)) := by
  obtain ⟨N1,hN1,hpoly⟩ := Compat.fixed_polynomial_le_rpow (4*(χ⁻¹+1)) T 2 (δ/4)
    (by positivity) hT (by positivity)
  obtain ⟨N2,hN2,hpref⟩ := Compat.fixed_polynomial_le_rpow 2 T 1 1
    (by norm_num) hT (by norm_num)
  obtain ⟨N3,hN3,hexp⟩ := powerExp_eventually_le
    (by positivity : 0 < δ/4) (by linarith : δ/8 < δ/4) (by norm_num : (0:ℝ)<1) 1
  refine ⟨max N1 (max N2 N3),hN1.trans (le_max_left _ _),?_⟩
  intro N d hN hd F hF
  have hn1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hn2 : N2 ≤ N := (le_max_left N2 N3).trans ((le_max_right _ _).trans hN)
  have hn3 : N3 ≤ N := (le_max_right N2 N3).trans ((le_max_right _ _).trans hN)
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNge : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hp : 4*(χ⁻¹+1)*((d : ℝ)+1)^2 ≤ (N : ℝ)^(δ/4) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hpoly N d hn1 hd
  have hpre : 2*((d : ℝ)+1) ≤ N := by
    simpa only [Nat.cast_add,Nat.cast_one,pow_one,Real.rpow_one] using hpref N d hn2 hd
  let w : ℝ := (N : ℝ)^(F+δ/4)
  let V : ℝ := (N : ℝ)^(2*F)
  let t : ℝ := (N : ℝ)^(δ/4)
  have hw : 0<w := Real.rpow_pos_of_pos hNpos _
  have hV : 0<V := Real.rpow_pos_of_pos hNpos _
  have ht : 0<t := Real.rpow_pos_of_pos hNpos _
  have hwV : w≤V := Real.rpow_le_rpow_of_exponent_le hNge (by linarith)
  have hsquare : w^2 = V*t^2 := by
    dsimp [w,V,t]
    rw [pow_two,pow_two,← Real.rpow_add hNpos,← Real.rpow_add hNpos,
      ← Real.rpow_add hNpos]
    congr 1
    ring
  let den : ℝ := 4*((d : ℝ)+1)^2*(χ⁻¹*V+w)
  have hdenpos : 0<den := by dsimp [den]; positivity
  have hden : den≤V*t := by
    calc
      _ ≤ 4*((d : ℝ)+1)^2*(χ⁻¹*V+V) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hwV) (by positivity)
      _ = (4*(χ⁻¹+1)*((d : ℝ)+1)^2)*V := by ring
      _ ≤ t*V := mul_le_mul_of_nonneg_right hp hV.le
      _ = _ := mul_comm _ _
  have hratio : t ≤ w^2/den := by
    apply (le_div_iff₀ hdenpos).mpr
    calc
      _ ≤ t*(V*t) := mul_le_mul_of_nonneg_left hden ht.le
      _ = V*t^2 := by ring
      _ = _ := hsquare.symm
  have htail : Real.exp (-w^2/den) ≤ Real.exp (-t) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg hratio
  calc
    _ = (2*((d : ℝ)+1))*Real.exp (-w^2/den) := rfl
    _ ≤ (N : ℝ)*Real.exp (-t) :=
      mul_le_mul hpre htail (Real.exp_pos _).le (by positivity)
    _ ≤ _ := by simpa only [Real.rpow_one,one_mul,neg_one_mul,t] using hexp N hn3

/-- The complete finite block-count multiplier is absorbed at the source rate. -/
theorem countedWindowError_rate (k : ℕ) (hk : 1 ≤ k) (T δ : ℝ)
    (hT : 0 ≤ T) (hδ : 0 < δ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N d : ℕ, N0 ≤ N →
      (d : ℝ) ≤ T*Real.log (N : ℝ) →
      ((d : ℝ)+1)*(k : ℝ)^d*Real.exp (-(N : ℝ)^(δ/16)) ≤
        Real.exp (-(N : ℝ)^(δ/32)) := by
  obtain ⟨N1,hN1,hpref⟩ := Compat.fixed_polynomial_le_rpow 1 T 1 1
    (by norm_num) hT (by norm_num)
  obtain ⟨N2,hN2,hexp⟩ := powerExp_eventually_le
    (by positivity : 0<δ/16) (by linarith : δ/32<δ/16) (by norm_num : (0:ℝ)<1)
    (1+T*Real.log (k : ℝ))
  refine ⟨max N1 N2,hN1.trans (le_max_left _ _),?_⟩
  intro N d hN hd
  have hn1 : N1≤N := (le_max_left _ _).trans hN
  have hn2 : N2≤N := (le_max_right _ _).trans hN
  have hn0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hlogk : 0≤Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hpre : (d : ℝ)+1≤N := by
    simpa only [Nat.cast_add,Nat.cast_one,pow_one,Real.rpow_one,one_mul] using hpref N d hn1 hd
  have hpow : (k : ℝ)^d ≤ (N : ℝ)^(T*Real.log (k : ℝ)) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos hk0,Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hd hlogk
    nlinarith
  have hfull : ((d : ℝ)+1)*(k : ℝ)^d ≤ (N : ℝ)^(1+T*Real.log (k : ℝ)) := by
    calc
      _ ≤ (N : ℝ)*(N : ℝ)^(T*Real.log (k : ℝ)) :=
        mul_le_mul hpre hpow (pow_nonneg hk0.le _) hn0.le
      _ = _ := by rw [Real.rpow_add hn0,Real.rpow_one]
  exact (mul_le_mul_of_nonneg_right hfull (Real.exp_pos _).le).trans
    (by simpa only [one_mul,neg_one_mul] using hexp N hn2)

end RiffleUpperV2
