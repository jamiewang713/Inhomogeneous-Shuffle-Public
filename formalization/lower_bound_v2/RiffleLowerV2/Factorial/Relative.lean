import RiffleLowerV2.Factorial.ResidualEstimates

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiffleLowerV2.Factorial
open TimeProfile

theorem requestedCount_sum {k K d : ℕ} (w : Fin d → Word k K) (r : Fin d → ℕ)
    (j : Fin K) : ∑ a, requestedCount w r j a = ∑ i, r i := by
  simp only [requestedCount]
  rw [Finset.sum_comm]
  simp

theorem requestedCount_le {k K d : ℕ} (w : Fin d → Word k K) (r : Fin d → ℕ)
    (j : Fin K) (a : Fin k) : requestedCount w r j a ≤ ∑ i, r i := by
  rw [← requestedCount_sum w r j]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem requestedCount_pos_selected {k K d : ℕ} (w : Fin d → Word k K) (r : Fin d → ℕ)
    (j : Fin K) (a : Fin k) (ha : 0 < requestedCount w r j a) :
    ∃ i, (w i).get j = a := by
  by_contra hn
  have hh : requestedCount w r j a = 0 := by
    simp [requestedCount, show ∀ i, (w i).get j ≠ a from by simpa using hn]
  omega

theorem requested_monomial {k K d : ℕ} (w : Fin d → Word k K) (r : Fin d → ℕ)
    (j : Fin K) (n : Fin k → ℝ) :
    ∏ a, (n a)^requestedCount w r j a = ∏ i, (n ((w i).get j))^(r i) := by
  simp only [requestedCount]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp

theorem factorial_benchmark_identity {N k K d : ℕ} (cuts : Cuts k N K)
    (w : Fin d → Word k K) (r : Fin d → ℕ) :
    ∏ i, ((N : ℝ)*wordMass cuts (w i))^(r i) =
      (N : ℝ)^(∑ i, r i) *
      ∏ j, ((∏ a, (cuts.count j a : ℝ)^requestedCount w r j a) /
        (N : ℝ)^(∑ i, r i)) := by
  simp_rw [wordMean_eq_numericalMean, numericalMean, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, requested_monomial]

theorem numericalMean_product_benchmark {k K d : ℕ} (M : ℝ)
    (n : Fin K → Fin k → ℝ) (w : Fin d → Word k K) (r : Fin d → ℕ) :
    ∏ i, (numericalMean M (fun j => n j ((w i).get j)))^(r i) =
      numericalMean (M^(∑ i, r i)) (fun j => ∏ a, (n j a)^requestedCount w r j a) := by
  simp only [numericalMean, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, requested_monomial]

/-- One column, including unrequested piles of size zero. -/
theorem column_log_factorial_bound {k N R : ℕ} (n m : Fin k → ℕ) {c : ℝ}
    (hc : 0 < c) (hN : 0 < N) (hm : ∑ a, m a = R)
    (hs : ∀ a, 0 < m a → c*N ≤ (n a : ℝ)) (hR : 2*(R : ℝ) ≤ c*N) :
    0 < ∏ a, falling (n a) (m a) ∧
    0 < ∏ a, (n a : ℝ)^(m a) ∧
    |Real.log ((∏ a, falling (n a) (m a)) / (∏ a, (n a : ℝ)^(m a)))| ≤
      (R : ℝ)^2/(c*N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR (a) : m a ≤ R := by
    rw [← hm]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hpos (a) : 0 < falling (n a) (m a) ∧ 0 < (n a : ℝ)^(m a) := by
    by_cases hz : m a = 0
    · simp [hz, falling]
    · have hma : 0 < m a := Nat.pos_of_ne_zero hz
      have hna : 0 < n a := by exact_mod_cast (lt_of_lt_of_le (mul_pos hc hNr) (hs a hma))
      have hmn : m a ≤ n a := by
        have : (m a : ℝ) ≤ R := by exact_mod_cast hmR a
        have : (m a : ℝ) ≤ n a := by nlinarith [hs a hma]
        exact_mod_cast this
      constructor
      · unfold falling
        exact_mod_cast (Nat.descFactorial_pos.mpr hmn)
      · positivity
  have hp := Finset.prod_pos (fun a (_ : a ∈ Finset.univ) => (hpos a).1)
  have hq := Finset.prod_pos (fun a (_ : a ∈ Finset.univ) => (hpos a).2)
  refine ⟨hp, hq, ?_⟩
  have hlocal (a) : |Real.log (fallingCorrection (n a) (m a))| ≤ (m a : ℝ)^2/(c*N) := by
    by_cases hz : m a = 0
    · simp [hz]
    · have hma : 0 < m a := Nat.pos_of_ne_zero hz
      have hnR := hs a hma
      have hna : 0 < n a := by exact_mod_cast (lt_of_lt_of_le (mul_pos hc hNr) hnR)
      have h2m : 2*m a ≤ n a := by
        have : (m a : ℝ) ≤ R := by exact_mod_cast hmR a
        have : (2 : ℝ)*m a ≤ n a := by nlinarith
        exact_mod_cast this
      exact (log_fallingCorrection_bound hna h2m).trans
        (div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hc hNr) hnR)
  rw [← Finset.prod_div_distrib]
  change |Real.log (∏ a, fallingCorrection (n a) (m a))| ≤ _
  rw [Real.log_prod (f := fun a => fallingCorrection (n a) (m a))
    (fun a _ => (div_pos (hpos a).1 (hpos a).2).ne')]
  calc
    _ ≤ ∑ a, |Real.log (fallingCorrection (n a) (m a))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (m a : ℝ)^2/(c*N) := Finset.sum_le_sum fun a _ => hlocal a
    _ = (∑ a, (m a : ℝ)^2)/(c*N) := by rw [Finset.sum_div]
    _ ≤ (R : ℝ)^2/(c*N) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hc.le hNr.le)
      have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun a => (m a : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      have hcast : ∑ a, (m a : ℝ) = (R : ℝ) := by exact_mod_cast hm
      simpa only [hcast] using hh

/-- Pure numerical comparison, with a separate ambient population for residual applications. -/
theorem relativeFactorial_finite {N M K k R : ℕ} (n m : Fin K → Fin k → ℕ) {c : ℝ}
    (hc : 0 < c) (hN : 0 < N) (hM : c*N ≤ (M : ℝ))
    (hm : ∀ j, ∑ a, m j a = R)
    (hs : ∀ j a, 0 < m j a → c*N ≤ (n j a : ℝ))
    (hR : 2*(R : ℝ) ≤ c*N)
    (he : (2/c)*(K+1)*(R : ℝ)^2/N ≤ 1) :
    |numericalMean (falling M R) (fun j => ∏ a, falling (n j a) (m j a)) -
      numericalMean ((M : ℝ)^R) (fun j => ∏ a, (n j a : ℝ)^(m j a))| ≤
      (4/c)*(K+1)*(R : ℝ)^2/N *
        numericalMean ((M : ℝ)^R) (fun j => ∏ a, (n j a : ℝ)^(m j a)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMp : 0 < M := by exact_mod_cast (lt_of_lt_of_le (mul_pos hc hNr) hM)
  have h2R : 2*R ≤ M := by exact_mod_cast hR.trans hM
  have hRM : R ≤ M := by omega
  have hMf : 0 < falling M R := by unfold falling; exact_mod_cast (Nat.descFactorial_pos.mpr hRM)
  have hMpR : (0 : ℝ) < (M : ℝ)^R := by positivity
  have hcols j := column_log_factorial_bound (n j) (m j) hc hN (hm j) (hs j) hR
  have hlogM : |Real.log (falling M R / (M : ℝ)^R)| ≤ (R : ℝ)^2/(c*N) :=
    (log_fallingCorrection_bound hMp h2R).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hc hNr) hM)
  have hl := numericalMean_log_ratio_bound hMpR hMf (fun j => (hcols j).2.1)
    (fun j => (hcols j).1) hlogM (fun j => (hcols j).2.2)
  have hb : (R : ℝ)^2/(c*N) + (K : ℝ)*((R : ℝ)^2/(c*N)+(R : ℝ)^2/(c*N)) ≤
      (2/c)*(K+1)*(R : ℝ)^2/N := by
    field_simp
    nlinarith [sq_nonneg (R : ℝ)]
  have hf := relative_error_of_log (numericalMean_pos hMf fun j => (hcols j).1)
    (numericalMean_pos hMpR fun j => (hcols j).2.1) (hl.trans hb) he
  convert hf using 1 <;> ring

end RiffleLowerV2.Factorial
