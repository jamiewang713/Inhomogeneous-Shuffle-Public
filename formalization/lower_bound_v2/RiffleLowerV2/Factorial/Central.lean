import RiffleLowerV2.Factorial.PolynomialMoments
import RiffleLowerV2.Factorial.Bonferroni
import RiffleLowerV2.Factorial.PoissonPolynomial

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Factorial

variable {Ω : Type*} [Fintype Ω]

theorem probability_polynomial_error (P : PMF Ω) (A : Ω → Prop) (U D : Ω → ℝ)
    (h : ∀ ω, 0 ≤ U ω - (if A ω then 1 else 0) ∧
      U ω - (if A ω then 1 else 0) ≤ D ω) :
    |probability P A - expect P U| ≤ expect P D := by
  have hlo : probability P A ≤ expect P U := by
    apply expect_mono
    intro ω
    exact sub_nonneg.mp (h ω).1
  have hhi : expect P U ≤ probability P A + expect P D := by
    rw [probability, ← expect_add]
    apply expect_mono
    intro ω
    linarith [(h ω).2]
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith

/-- One-variable finite factorial comparison; the polynomial remainder is integrated. -/
theorem centralComparisonOne : Targets.CentralComparisonOne := by
  intro Ω _ P X μ ε m hμ hε hε1 hm hme hmoment
  have hp := bonferroni_expect_error P X μ ε m hmoment
  have ha := probability_polynomial_error P (fun ω => 2 ≤ X ω)
    (fun ω => bonferroni m (X ω)) (fun ω => bonferroniRemainder m (X ω)) (by
      intro ω
      have hh := bonferroniSandwich m hm hme (X ω)
      by_cases hx : 2 ≤ X ω <;> simpa [hx] using hh)
  have hd := expect_remainder_le P X μ ε m (hmoment m le_rfl)
  have hs := poissonPolynomial_sandwich m hm hme μ hμ.le
  have hc := poissonCoefficientSum_le m μ hμ.le
  have hr : 0 ≤ poissonRemainder m μ := by unfold poissonRemainder; positivity
  have hb : |poissonPolynomial m μ - poissonCollision μ| ≤ poissonRemainder m μ := by
    rw [abs_of_nonneg hs.1]
    exact hs.2
  have he : |expect P (fun ω => bonferroni m (X ω)) - poissonPolynomial m μ| ≤
      ε * ((1+μ)*Real.exp μ) := by
    exact hp.trans (mul_le_mul_of_nonneg_left hc hε)
  have ht := (abs_sub_le (probability P (fun ω => 2 ≤ X ω))
    (expect P (fun ω => bonferroni m (X ω))) (poissonCollision μ)).trans
      (add_le_add (ha.trans hd) ((abs_sub_le
        (expect P (fun ω => bonferroni m (X ω)))
        (poissonPolynomial m μ) (poissonCollision μ)).trans (add_le_add he hb)))
  nlinarith [mul_le_mul_of_nonneg_right hε1 hr]

/-- Two-variable comparison uses the (m,m) moment to control the full product remainder. -/
theorem centralComparison : Targets.CentralComparison := by
  intro Ω _ P X Y μ ν ε m hμ hν hε hε1 hm hme hmoment
  have hX (r : ℕ) (hr : r ≤ m) :
      |expect P (fun ω => falling (X ω) r) - μ^r| ≤ ε*μ^r := by
    simpa [falling] using hmoment r 0 (by omega)
  have hY (s : ℕ) (hs : s ≤ m) :
      |expect P (fun ω => falling (Y ω) s) - ν^s| ≤ ε*ν^s := by
    simpa [falling] using hmoment 0 s (by omega)
  have hp := bonferroni_product_expect_error P X Y μ ν ε m hmoment
  have ha := probability_polynomial_error P (fun ω => 2 ≤ X ω ∧ 2 ≤ Y ω)
    (fun ω => bonferroni m (X ω) * bonferroni m (Y ω))
    (fun ω => bonferroniRemainder m (X ω) + bonferroniRemainder m (Y ω) +
      bonferroniRemainder m (X ω) * bonferroniRemainder m (Y ω)) (by
      intro ω
      have hh := bonferroniProduct m hm hme (X ω) (Y ω)
      by_cases hx : 2 ≤ X ω ∧ 2 ≤ Y ω <;> simpa [hx] using hh)
  rw [expect_add, expect_add] at ha
  have hdX := expect_remainder_le P X μ ε m (hX m le_rfl)
  have hdY := expect_remainder_le P Y ν ε m (hY m le_rfl)
  have hdXY := expect_remainder_product_le P X Y μ ν ε m (hmoment m m (by omega))
  let T := poissonRemainder m μ + poissonRemainder m ν + poissonRemainder m μ * poissonRemainder m ν
  have hT : 0 ≤ T := by dsimp [T, poissonRemainder]; positivity
  have hactual : |probability P (fun ω => 2 ≤ X ω ∧ 2 ≤ Y ω) -
      expect P (fun ω => bonferroni m (X ω) * bonferroni m (Y ω))| ≤ (1+ε)*T := by
    calc
      _ ≤ _ := ha
      _ ≤ (1+ε)*poissonRemainder m μ + (1+ε)*poissonRemainder m ν +
          (1+ε)*(poissonRemainder m μ*poissonRemainder m ν) := add_le_add (add_le_add hdX hdY) hdXY
      _ = _ := by dsimp [T]; ring
  have hsμ := poissonPolynomial_sandwich m hm hme μ hμ.le
  have hsν := poissonPolynomial_sandwich m hm hme ν hν.le
  have hfμ := poissonCollision_bounds μ hμ.le
  have hfν := poissonCollision_bounds ν hν.le
  have hscalar := product_remainder (poissonPolynomial m μ) (poissonPolynomial m ν)
    (poissonCollision μ) (poissonCollision ν) (poissonRemainder m μ) (poissonRemainder m ν)
    hfμ.1 hfμ.2 hfν.1 hfν.2 hsμ hsν
  have hbenchmark : |poissonPolynomial m μ * poissonPolynomial m ν -
      poissonCollision μ * poissonCollision ν| ≤ T := by
    rw [abs_of_nonneg hscalar.1]
    exact hscalar.2
  have hcμ := poissonCoefficientSum_le m μ hμ.le
  have hcν := poissonCoefficientSum_le m ν hν.le
  have hcμ0 : 0 ≤ ∑ r ∈ Finset.Icc 2 m, (r-1 : ℕ) * μ^r / (r.factorial : ℝ) := by
    apply Finset.sum_nonneg
    intro r _
    positivity
  have hcν0 : 0 ≤ ∑ s ∈ Finset.Icc 2 m, (s-1 : ℕ) * ν^s / (s.factorial : ℝ) := by
    apply Finset.sum_nonneg
    intro s _
    positivity
  have he : |expect P (fun ω => bonferroni m (X ω) * bonferroni m (Y ω)) -
      poissonPolynomial m μ * poissonPolynomial m ν| ≤
      ε*(1+μ)*(1+ν)*Real.exp (μ+ν) := by
    calc
      _ ≤ _ := hp
      _ ≤ ε * ((1+μ)*Real.exp μ) * ((1+ν)*Real.exp ν) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcμ hε) hcν hcν0 (by positivity)
      _ = _ := by rw [Real.exp_add]; ring
  have ht := (abs_sub_le (probability P (fun ω => 2 ≤ X ω ∧ 2 ≤ Y ω))
    (expect P (fun ω => bonferroni m (X ω) * bonferroni m (Y ω)))
    (poissonCollision μ * poissonCollision ν)).trans
      (add_le_add hactual ((abs_sub_le
        (expect P (fun ω => bonferroni m (X ω) * bonferroni m (Y ω)))
        (poissonPolynomial m μ * poissonPolynomial m ν)
        (poissonCollision μ * poissonCollision ν)).trans (add_le_add he hbenchmark)))
  change _ ≤ ε*(1+μ)*(1+ν)*Real.exp (μ+ν) + 3*T
  nlinarith [mul_le_mul_of_nonneg_right hε1 hT]

end RiffleLowerV2.Factorial
