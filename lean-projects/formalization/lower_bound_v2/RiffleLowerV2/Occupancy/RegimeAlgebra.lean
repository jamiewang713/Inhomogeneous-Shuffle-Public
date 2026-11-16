import RiffleLowerV2.Occupancy.FiniteProbability
import RiffleLowerV2.Occupancy.Poisson

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Occupancy

/-- A weighted rare-count sandwich remains relative even when its weight is zero. -/
theorem rare_sandwich_error {μ τ η q p E2 E3 : ℝ}
    (hμ : 0 ≤ μ) (hμτ : μ ≤ τ) (hτ : τ ≤ 1/2)
    (_hη0 : 0 ≤ η) (hητ : η ≤ τ) (hq : 0 ≤ q)
    (hE2 : |E2 - μ^2*q| ≤ η*μ^2*q)
    (hE3 : |E3 - μ^3*q| ≤ η*μ^3*q)
    (hlo : E2/2 - E3/3 ≤ p) (hhi : p ≤ E2/2) :
    |p - μ^2*q/2| ≤ τ*μ^2*q := by
  have hM : 0 ≤ μ^2*q := mul_nonneg (sq_nonneg μ) hq
  have hM3 : 0 ≤ μ^3*q := mul_nonneg (pow_nonneg hμ _) hq
  have h2 := abs_le.mp hE2
  have h3 := abs_le.mp hE3
  have he := mul_le_mul_of_nonneg_right hητ hM
  have he3 := mul_le_mul_of_nonneg_right (hητ.trans hτ) hM3
  have hm := mul_le_mul_of_nonneg_right hμτ hM
  have hτ0 : 0 ≤ τ := hμ.trans hμτ
  have hτM : 0 ≤ τ*μ^2*q := mul_nonneg (mul_nonneg hτ0 (sq_nonneg μ)) hq
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Rare one-category collision probability, with an explicit relative constant. -/
theorem rare_marginal_relative {μ τ η p E2 E3 : ℝ}
    (hμ : 0 < μ) (hμτ : μ ≤ τ) (hτ : τ ≤ 1/2)
    (hη0 : 0 ≤ η) (hητ : η ≤ τ)
    (hE2 : |E2 - μ^2| ≤ η*μ^2)
    (hE3 : |E3 - μ^3| ≤ η*μ^3)
    (hlo : E2/2 - E3/3 ≤ p) (hhi : p ≤ E2/2) :
    |p - poissonCollision μ| ≤ 8*τ*poissonCollision μ := by
  have hp : |p - μ^2/2| ≤ τ*μ^2 := by
    simpa using rare_sandwich_error hμ.le hμτ hτ hη0 hητ zero_le_one
      (by simpa using hE2) (by simpa using hE3) hlo hhi
  have hf := poissonCollision_rare μ hμ.le
  have hτ0 : 0 ≤ τ := hμ.le.trans hμτ
  have hm := mul_le_mul_of_nonneg_right hμτ (sq_nonneg μ)
  have hmhalf := mul_le_mul_of_nonneg_right (hμτ.trans hτ) (sq_nonneg μ)
  have hl : μ^2/4 ≤ poissonCollision μ := by nlinarith
  have he := mul_le_mul_of_nonneg_left hl hτ0
  have habs := abs_le.mp hp
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A convenient denominator lower bound from the same moment sandwich. -/
theorem rare_marginal_lower {μ τ η p E2 E3 : ℝ}
    (hμ : 0 ≤ μ) (hμτ : μ ≤ τ) (hτ : τ ≤ 1/4)
    (hη0 : 0 ≤ η) (hητ : η ≤ τ)
    (hE2 : |E2 - μ^2| ≤ η*μ^2)
    (hE3 : |E3 - μ^3| ≤ η*μ^3)
    (hlo : E2/2 - E3/3 ≤ p) (hhi : p ≤ E2/2) :
    μ^2/4 ≤ p := by
  have hp : |p - μ^2/2| ≤ τ*μ^2 := by
    simpa using rare_sandwich_error hμ hμτ (by linarith : τ ≤ 1/2)
      hη0 hητ zero_le_one (by simpa using hE2) (by simpa using hE3) hlo hhi
  have habs := (abs_le.mp hp).1
  have hbound := mul_le_mul_of_nonneg_right hτ (sq_nonneg μ)
  nlinarith

/-- Rare mixed-pair algebra. The other collision probability has no lower bound. -/
theorem rare_pair_relative {μ τ η p q joint E2 E3 F2 F3 : ℝ}
    (hμ : 0 < μ) (hμτ : μ ≤ τ) (hτ : τ ≤ 1/2)
    (hη0 : 0 ≤ η) (hητ : η ≤ τ) (hq : 0 ≤ q)
    (hE2 : |E2 - μ^2| ≤ η*μ^2) (hE3 : |E3 - μ^3| ≤ η*μ^3)
    (hF2 : |F2 - μ^2*q| ≤ η*μ^2*q)
    (hF3 : |F3 - μ^3*q| ≤ η*μ^3*q)
    (hplo : E2/2 - E3/3 ≤ p) (hphi : p ≤ E2/2)
    (hjlo : F2/2 - F3/3 ≤ joint) (hjhi : joint ≤ F2/2)
    (hp : μ^2/4 ≤ p) :
    |joint - p*q| ≤ 16*τ*p*q := by
  have hep : |p - μ^2/2| ≤ τ*μ^2 := by
    simpa using rare_sandwich_error hμ.le hμτ hτ hη0 hητ zero_le_one
      (by simpa using hE2) (by simpa using hE3) hplo hphi
  have hej := rare_sandwich_error hμ.le hμτ hτ hη0 hητ hq hF2 hF3 hjlo hjhi
  have heq := mul_le_mul_of_nonneg_right hep hq
  have hτ0 : 0 ≤ τ := hμ.le.trans hμτ
  have hpq := mul_le_mul_of_nonneg_right hp hq
  have hb := mul_le_mul_of_nonneg_left hpq hτ0
  have hprod : 0 ≤ τ*p*q :=
    mul_nonneg (mul_nonneg hτ0 ((by positivity : 0 ≤ μ^2/4).trans hp)) hq
  have htri : |joint - p*q| ≤ |joint - μ^2*q/2| + |(p-μ^2/2)*q| := by
    calc
      _ = |(joint-μ^2*q/2) - (p-μ^2/2)*q| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  rw [abs_mul, abs_of_nonneg hq] at htri
  nlinarith

/-- Convert a central absolute error relative to the benchmark product into
an error relative to the actual product after controlling both marginals. -/
theorem pair_relative_of_benchmark {p q joint f g ε δ : ℝ}
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hε0 : 0 ≤ ε) (hε : ε ≤ 1/2) (hδ : 0 ≤ δ)
    (hp : |p-f| ≤ ε*f) (hq : |q-g| ≤ ε*g)
    (hj : |joint-f*g| ≤ δ*f*g) :
    |joint-p*q| ≤ 4*(δ+3*ε)*p*q := by
  have hp' := abs_le.mp hp
  have hq' := abs_le.mp hq
  have hεf := mul_le_mul_of_nonneg_right hε hf
  have hεg := mul_le_mul_of_nonneg_right hε hg
  have hp0 : 0 ≤ p := by nlinarith
  have hq0 : 0 ≤ q := by nlinarith
  have hpl : f/2 ≤ p := by nlinarith
  have hql : g/2 ≤ q := by nlinarith
  have hqu : q ≤ 3/2*g := by nlinarith
  have hproduct := mul_le_mul hpl hql (by positivity : 0 ≤ g/2) hp0
  have hprod : f*g ≤ 4*p*q := by nlinarith
  have hmul1 := mul_le_mul_of_nonneg_right hp hq0
  have hmul2 := mul_le_mul_of_nonneg_left hq hf
  have hmul3 := mul_le_mul_of_nonneg_left hqu (mul_nonneg hε0 hf)
  have hεfg : 0 ≤ ε*f*g := mul_nonneg (mul_nonneg hε0 hf) hg
  have hbench : |p*q-f*g| ≤ 3*ε*f*g := by
    have ht : |p*q-f*g| ≤ |p-f| * q + f * |q-g| := by
      calc
        _ = |(p-f)*q + f*(q-g)| := by congr 1; ring
        _ ≤ _ := by
          simpa only [abs_mul, abs_of_nonneg hq0, abs_of_nonneg hf] using
            abs_add_le ((p-f)*q) (f*(q-g))
    nlinarith
  have htri : |joint-p*q| ≤ |joint-f*g| + |p*q-f*g| := by
    calc
      _ = |(joint-f*g) - (p*q-f*g)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hfactor : 0 ≤ δ+3*ε := by positivity
  have hbound := mul_le_mul_of_nonneg_left hprod hfactor
  nlinarith

/-- A large category's complement controls its covariance with every event. -/
theorem abs_probability_covariance_le_complement {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (A B : Ω → Prop) :
    |probability P (fun ω => A ω ∧ B ω) - probability P A * probability P B| ≤
      probability P (fun ω => ¬ B ω) := by
  have hsplit : probability P (fun ω => A ω ∧ B ω) +
      probability P (fun ω => A ω ∧ ¬ B ω) = probability P A := by
    rw [probability, probability, ← Factorial.expect_add]
    apply congrArg (expect P)
    funext ω
    by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb]
  have hnonneg := probability_nonneg P (fun ω => A ω ∧ ¬ B ω)
  have hle := probability_and_le_right P A (fun ω => ¬ B ω)
  have ha0 := probability_nonneg P A
  have ha1 := probability_le_one P A
  have hb0 := probability_nonneg P (fun ω => ¬ B ω)
  have hab0 := mul_nonneg ha0 hb0
  have hab1 := mul_le_mul_of_nonneg_right ha1 hb0
  have hnot := probability_not P B
  apply abs_le.mpr
  constructor <;> nlinarith

end RiffleLowerV2.Occupancy
