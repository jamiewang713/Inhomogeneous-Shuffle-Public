import RiffleLowerV2.Factorial.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Factorial

/-- Coefficient of the falling factorial, rather than of the binomial coefficient. -/
def factorialCoefficient (r : ℕ) : ℝ := (-1 : ℝ)^r * (r-1 : ℕ) / r.factorial

theorem factorialCoefficient_abs (r : ℕ) :
    |factorialCoefficient r| = (r-1 : ℕ) / (r.factorial : ℝ) := by
  simp [factorialCoefficient, abs_div, abs_mul, abs_pow]

theorem bonferroni_eq_factorial_sum (m n : ℕ) :
    bonferroni m n = ∑ r ∈ Finset.Icc 2 m, factorialCoefficient r * falling n r := by
  unfold bonferroni
  apply Finset.sum_congr rfl
  intro r _
  rw [choose_eq_falling_div]
  unfold factorialCoefficient
  ring

theorem remainder_eq_factorial (m n : ℕ) :
    bonferroniRemainder m n = ((m-1 : ℕ) / (m.factorial : ℝ)) * falling n m := by
  unfold bonferroniRemainder
  rw [choose_eq_falling_div]
  ring

theorem poissonRemainder_eq (m : ℕ) (t : ℝ) :
    poissonRemainder m t = ((m-1 : ℕ) / (m.factorial : ℝ)) * t^m := by
  unfold poissonRemainder
  ring

/-- A finite coefficient comparison; no event is removed from the expectation. -/
theorem polynomial_error {ι : Type*} (s : Finset ι) (a M T : ι → ℝ) (ε : ℝ)
    (h : ∀ i ∈ s, |M i - T i| ≤ ε * T i) :
    |(∑ i ∈ s, a i * M i) - ∑ i ∈ s, a i * T i| ≤
      ε * ∑ i ∈ s, |a i| * T i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |a i * M i - a i * T i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |a i| * (ε * T i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (h i hi) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

variable {Ω : Type*} [Fintype Ω]

theorem expect_bonferroni (P : PMF Ω) (X : Ω → ℕ) (m : ℕ) :
    expect P (fun ω => bonferroni m (X ω)) =
      ∑ r ∈ Finset.Icc 2 m, factorialCoefficient r * expect P (fun ω => falling (X ω) r) := by
  simp_rw [bonferroni_eq_factorial_sum]
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact expect_const_mul P _ _

theorem expect_bonferroni_product (P : PMF Ω) (X Y : Ω → ℕ) (m : ℕ) :
    expect P (fun ω => bonferroni m (X ω) * bonferroni m (Y ω)) =
      ∑ r ∈ Finset.Icc 2 m, ∑ s ∈ Finset.Icc 2 m,
        (factorialCoefficient r * factorialCoefficient s) *
          expect P (fun ω => falling (X ω) r * falling (Y ω) s) := by
  simp_rw [bonferroni_eq_factorial_sum, Finset.sum_mul, Finset.mul_sum]
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← expect_const_mul]
  congr 1
  ext ω
  ring

theorem bonferroni_expect_error (P : PMF Ω) (X : Ω → ℕ) (μ ε : ℝ) (m : ℕ)
    (h : ∀ r : ℕ, r ≤ m → |expect P (fun ω => falling (X ω) r) - μ^r| ≤ ε * μ^r) :
    |expect P (fun ω => bonferroni m (X ω)) -
      ∑ r ∈ Finset.Icc 2 m, (-1 : ℝ)^r * (r-1 : ℕ) * μ^r / r.factorial| ≤
      ε * ∑ r ∈ Finset.Icc 2 m, (r-1 : ℕ) * μ^r / r.factorial := by
  rw [expect_bonferroni]
  have hp := polynomial_error (Finset.Icc 2 m) factorialCoefficient
    (fun r => expect P (fun ω => falling (X ω) r)) (fun r => μ^r) ε
    (fun r hr => h r (Finset.mem_Icc.mp hr).2)
  simp_rw [factorialCoefficient_abs] at hp
  simpa only [factorialCoefficient, div_mul_eq_mul_div] using hp

theorem bonferroni_product_expect_error (P : PMF Ω) (X Y : Ω → ℕ) (μ ν ε : ℝ) (m : ℕ)
    (h : ∀ r s : ℕ, r+s ≤ 2*m →
      |expect P (fun ω => falling (X ω) r * falling (Y ω) s) - μ^r * ν^s| ≤ ε * μ^r * ν^s) :
    |expect P (fun ω => bonferroni m (X ω) * bonferroni m (Y ω)) -
      (∑ r ∈ Finset.Icc 2 m, (-1 : ℝ)^r * (r-1 : ℕ) * μ^r / r.factorial) *
      (∑ s ∈ Finset.Icc 2 m, (-1 : ℝ)^s * (s-1 : ℕ) * ν^s / s.factorial)| ≤
      ε * (∑ r ∈ Finset.Icc 2 m, (r-1 : ℕ) * μ^r / r.factorial) *
        (∑ s ∈ Finset.Icc 2 m, (s-1 : ℕ) * ν^s / s.factorial) := by
  let S := Finset.Icc 2 m
  have hp := polynomial_error (S ×ˢ S)
    (fun p => factorialCoefficient p.1 * factorialCoefficient p.2)
    (fun p => expect P (fun ω => falling (X ω) p.1 * falling (Y ω) p.2))
    (fun p => μ^p.1 * ν^p.2) ε (by
      intro p hp
      have hr := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2
      have hs := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).2
      simpa only [mul_assoc] using h p.1 p.2 (by omega))
  rw [expect_bonferroni_product]
  simp only [Finset.sum_product, abs_mul, factorialCoefficient_abs] at hp
  have heq (a b : ℝ) (r s : ℕ) :
      (factorialCoefficient r * factorialCoefficient s) * (a^r * b^s) =
        ((-1 : ℝ)^r * (r-1 : ℕ) * a^r / r.factorial) *
        ((-1 : ℝ)^s * (s-1 : ℕ) * b^s / s.factorial) := by
    unfold factorialCoefficient
    ring
  have hab (r s : ℕ) :
      ((r-1 : ℕ) / (r.factorial : ℝ) * ((s-1 : ℕ) / (s.factorial : ℝ))) * (μ^r * ν^s) =
        ((r-1 : ℕ) * μ^r / (r.factorial : ℝ)) * ((s-1 : ℕ) * ν^s / (s.factorial : ℝ)) := by ring
  simp_rw [heq, hab] at hp
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul] at hp
  simpa only [S, mul_assoc] using hp

theorem expect_remainder_le (P : PMF Ω) (X : Ω → ℕ) (μ ε : ℝ) (m : ℕ)
    (h : |expect P (fun ω => falling (X ω) m) - μ^m| ≤ ε * μ^m) :
    expect P (fun ω => bonferroniRemainder m (X ω)) ≤ (1+ε) * poissonRemainder m μ := by
  simp_rw [remainder_eq_factorial]
  rw [expect_const_mul, poissonRemainder_eq]
  have hm : expect P (fun ω => falling (X ω) m) ≤ (1+ε)*μ^m := by
    have hh := (le_abs_self _).trans h
    linarith
  have hc : 0 ≤ (m-1 : ℕ) / (m.factorial : ℝ) := by positivity
  calc
    _ ≤ ((m-1 : ℕ) / (m.factorial : ℝ)) * ((1+ε)*μ^m) :=
      mul_le_mul_of_nonneg_left hm hc
    _ = _ := by ring

theorem expect_remainder_product_le (P : PMF Ω) (X Y : Ω → ℕ) (μ ν ε : ℝ) (m : ℕ)
    (h : |expect P (fun ω => falling (X ω) m * falling (Y ω) m) - μ^m * ν^m| ≤ ε * μ^m * ν^m) :
    expect P (fun ω => bonferroniRemainder m (X ω) * bonferroniRemainder m (Y ω)) ≤
      (1+ε) * (poissonRemainder m μ * poissonRemainder m ν) := by
  have heq : (fun ω => bonferroniRemainder m (X ω) * bonferroniRemainder m (Y ω)) =
      (fun ω => (((m-1 : ℕ) / (m.factorial : ℝ))^2) *
        (falling (X ω) m * falling (Y ω) m)) := by
    ext ω
    rw [remainder_eq_factorial, remainder_eq_factorial]
    ring
  rw [heq, expect_const_mul, poissonRemainder_eq, poissonRemainder_eq]
  have hm : expect P (fun ω => falling (X ω) m * falling (Y ω) m) ≤ (1+ε)*(μ^m*ν^m) := by
    have hh := (le_abs_self _).trans h
    linarith
  calc
    _ ≤ (((m-1 : ℕ) / (m.factorial : ℝ))^2) * ((1+ε)*(μ^m*ν^m)) :=
      mul_le_mul_of_nonneg_left hm (sq_nonneg _)
    _ = _ := by ring

end RiffleLowerV2.Factorial
