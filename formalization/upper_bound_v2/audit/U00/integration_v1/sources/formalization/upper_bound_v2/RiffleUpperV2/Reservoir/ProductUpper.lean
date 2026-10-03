import RiffleUpperV2.Reservoir.ReserveWeight
import RiffleUpperV2.GraphOverlap.FactorialTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiffleUpperV2.Reservoir

theorem regular_coordinate_ratio {c m R : ℕ} {p τ δ err : ℝ}
    (hp : τ≤p) (hp0 : 0≤p) (hτ : 0<τ) (hδ : 0≤δ)
    (hm : m≤2) (hM : 0<c+m)
    (hbudget : err+2 ≤ (c+m : ℕ)*τ*δ)
    (hcount : |(R:ℝ)-(c:ℝ)*p|≤err+m) :
    (R:ℝ)/(c+m : ℕ) ≤ p*(1+δ) := by
  have hmc : (m:ℝ)≤2 := by exact_mod_cast hm
  have hhigh := (abs_le.mp hcount).2
  have hmcast : ((c+m:ℕ):ℝ)=(c:ℝ)+m := Nat.cast_add c m
  have hδp : ((c+m:ℕ):ℝ)*τ*δ ≤ ((c+m:ℕ):ℝ)*p*δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) hδ
  apply (div_le_iff₀ (by exact_mod_cast hM : (0:ℝ)<(c+m:ℕ))).mpr
  have hmp : 0≤(m:ℝ)*p := mul_nonneg (Nat.cast_nonneg _) hp0
  nlinarith

theorem rare_coordinate_ratio {M R n : ℕ} {p g : ℝ}
    (hg : 0<g) (hn : 0<n) (hp : 0≤p)
    (hcount : (R:ℝ)≤n*p) (hM : g*n≤M) :
    (R:ℝ)/M ≤ p/g := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hM' : (0:ℝ)<M := lt_of_lt_of_le (mul_pos hg hn') hM
  apply (div_le_div_iff₀ hM' hg).mpr
  have h1 := mul_le_mul_of_nonneg_right hcount hg.le
  have h2 := mul_le_mul_of_nonneg_left hM hp
  nlinarith

theorem rareExponent_identity {g τ : ℝ} (hg : 0<g) (hτ : 0<τ) (hτ1 : τ<1) :
    τ^(Real.log (1/g)/Real.log (1/τ))=g := by
  rw [one_div,one_div,Real.log_inv,Real.log_inv,neg_div_neg_eq]
  rw [Real.rpow_def_of_pos hτ]
  have hlog : Real.log τ≠0 := ne_of_lt (Real.log_neg hτ hτ1)
  rw [mul_div_cancel₀ _ hlog,Real.exp_log hg]

theorem rareExponent_nonneg {g τ : ℝ} (hg : 0<g) (hg1 : g<1)
    (hτ : 0<τ) (hτ1 : τ<1) : 0≤Real.log (1/g)/Real.log (1/τ) := by
  rw [one_div,one_div,Real.log_inv,Real.log_inv,neg_div_neg_eq]
  exact (div_pos_of_neg_of_neg (Real.log_neg hg hg1) (Real.log_neg hτ hτ1)).le

/-- Both regular and rare coordinates share a power-law upper envelope.
The zero-mass case is retained since 1-alpha is strictly positive. -/
theorem coordinate_power_envelope {p τ g α δ x : ℝ}
    (hp0 : 0≤p) (hp1 : p≤1) (hτ : 0<τ) (hg : 0<g)
    (hα0 : 0≤α) (hα1 : α<1) (hτg : τ^α=g) (hδ : 0≤δ)
    (hreg : τ≤p → x≤p*(1+δ)) (hrare : p<τ → x≤p/g) :
    x≤(1+δ)*p^(1-α) := by
  by_cases hp : τ≤p
  · apply (hreg hp).trans
    have hpow : p≤p^(1-α) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge'
        hp0 hp1 (by linarith : 0≤1-α) (by linarith : 1-α≤1)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpow (by linarith : 0≤1+δ)
  · apply (hrare (lt_of_not_ge hp)).trans
    have hpow : p/g≤p^(1-α) := by
      by_cases hpz : p=0
      · simp [hpz,Real.zero_rpow (by linarith : 1-α≠0)]
      have hpp : 0<p := lt_of_le_of_ne hp0 (Ne.symm hpz)
      have hle : p^α≤g := by rw [← hτg]; exact Real.rpow_le_rpow hp0 (le_of_not_ge hp) hα0
      apply (div_le_iff₀ hg).mpr
      have heq : p^(1-α)*p^α=p := by rw [← Real.rpow_add hpp]; simp
      calc
        _ = p^(1-α)*p^α := heq.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hp0 _)
    apply hpow.trans
    nlinarith [Real.rpow_nonneg hp0 (1-α)]

/-- Product control retains the exact exponent m(1-alpha) and the source
factor 2^m. Zero coordinates remain zero throughout. -/
theorem product_power_envelope {ι : Type*} (J : Finset ι) (M m : ℕ)
    (R : ι → ℕ) (p : ι → ℝ) (α δ : ℝ)
    (hp : ∀ j∈J, 0≤p j) (hR : ∀ j∈J, R j≤M) (hδ : 0≤δ)
    (henv : ∀ j∈J, (R j:ℝ)/M≤(1+δ)*(p j)^(1-α))
    (herror : (1+δ)^J.card≤2) :
    (∏ j∈J, RiffleLowerV2.falling (R j) m / RiffleLowerV2.falling M m) ≤
      2^m * (∏ j∈J, p j)^((m:ℝ)*(1-α)) := by
  have hprod : (∏ j∈J, RiffleLowerV2.falling (R j) m / RiffleLowerV2.falling M m) ≤
      ∏ j∈J, ((1+δ)*(p j)^(1-α))^m := by
    apply Finset.prod_le_prod
    · intro j hj
      unfold RiffleLowerV2.falling
      positivity
    · intro j hj
      exact (GraphOverlap.descFactorial_ratio_le_pow (hR j hj) m).trans
        (pow_le_pow_left₀ (by positivity) (henv j hj) m)
  have heq : (∏ j∈J, ((1+δ)*(p j)^(1-α))^m) =
      ((1+δ)^J.card)^m * (∏ j∈J, p j)^((m:ℝ)*(1-α)) := by
    rw [Finset.prod_pow,Finset.prod_mul_distrib,Finset.prod_const,Real.finsetProd_rpow J p hp,mul_pow]
    congr 1
    rw [← Real.rpow_natCast,← Real.rpow_mul (Finset.prod_nonneg hp)]
    congr 1
    ring
  rw [heq] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (pow_nonneg (by linarith) _) herror m)
    (Real.rpow_nonneg (Finset.prod_nonneg hp) _))

/-- The logarithmic number of regular-coordinate errors is uniformly at
most two for all sufficiently large populations. -/
theorem eventual_logarithmic_error (C T : ℝ) (hC : 0≤C) (hT : 0<T) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ K : ℕ,
      (K:ℝ)≤T*Real.log (n:ℝ) →
      (1+C/(n:ℝ)^((1:ℝ)/3))^K≤2 := by
  open Filter in
  have hlim : Tendsto (fun n : ℕ => (C*T)*(Real.log (n:ℝ)/(n:ℝ)^((1:ℝ)/3))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using tendsto_const_nhds.mul
      ((isLittleO_log_rpow_atTop (by norm_num : 0<(1:ℝ)/3)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N0,hN0⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hlog)
  refine ⟨max N0 1,le_max_right _ _,?_⟩
  intro n hn K hK
  have hn1 : 1≤n := (le_max_right _ _).trans hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hpow : 0<(n:ℝ)^((1:ℝ)/3) := Real.rpow_pos_of_pos hn0 _
  have herr : (C/(n:ℝ)^((1:ℝ)/3))*(K:ℝ)≤Real.log 2 := by
    calc
      _ ≤ (C/(n:ℝ)^((1:ℝ)/3))*(T*Real.log (n:ℝ)) :=
        mul_le_mul_of_nonneg_left hK (div_nonneg hC hpow.le)
      _ = (C*T)*(Real.log (n:ℝ)/(n:ℝ)^((1:ℝ)/3)) := by ring
      _ ≤ _ := (hN0 n ((le_max_left _ _).trans hn)).le
  calc
    _ ≤ (Real.exp (C/(n:ℝ)^((1:ℝ)/3)))^K :=
      pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp (C/(n:ℝ)^((1:ℝ)/3))) K
    _ = Real.exp ((C/(n:ℝ)^((1:ℝ)/3))*(K:ℝ)) := by rw [mul_comm,Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr herr
    _ = _ := Real.exp_log (by norm_num)

end RiffleUpperV2.Reservoir
