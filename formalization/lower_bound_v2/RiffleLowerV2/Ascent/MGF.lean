import RiffleLowerV2.Ascent.FiniteProbability
import Mathlib.Probability.Moments.SubGaussian

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Ascent

variable {Ω : Type*} [Fintype Ω]

/-- Hoeffding's bounded-variable estimate specialized to finite indicators. -/
theorem bernoulli_mgf (P : PMF Ω) (A : Ω → Prop) (t : ℝ) :
    expect P (fun ω => Real.exp (t * ((if A ω then 1 else 0) - probability P A))) ≤
      Real.exp (t ^ 2 / 8) := by
  let : MeasurableSpace Ω := ⊤
  let : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  have hm : Measurable (fun ω => if A ω then (1 : ℝ) else 0) :=
    measurable_of_countable _
  have hb : ∀ᵐ ω ∂P.toMeasure, (if A ω then (1 : ℝ) else 0) ∈ Set.Icc 0 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    by_cases h : A ω <;> simp [h]
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm.aemeasurable hb).mgf_le t
  rw [expect_eq_integral]
  simp only [probability, expect_eq_integral]
  simp [ProbabilityTheory.mgf] at h
  convert h using 1
  congr 1
  ring

theorem bernoulliMGF : Targets.BernoulliMGF := by
  intro Ω _ P A t
  exact bernoulli_mgf P A t

/-- A class of centered indicators whose exponential factors have a product expectation.
The factorization must be discharged from the concrete within-class joint law. -/
theorem one_class_mgf {I : Type*} (P : PMF Ω) (s : Finset I) (A : I → Ω → Prop)
    (hfactor : ∀ u : ℝ,
      expect P (fun ω => ∏ i ∈ s,
        Real.exp (u * ((if A i ω then 1 else 0) - probability P (A i)))) =
      ∏ i ∈ s, expect P (fun ω =>
        Real.exp (u * ((if A i ω then 1 else 0) - probability P (A i))))) (u : ℝ) :
    expect P (fun ω => Real.exp (u * ∑ i ∈ s,
      ((if A i ω then 1 else 0) - probability P (A i)))) ≤
      Real.exp (u ^ 2 * s.card / 8) := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [hfactor]
  calc
    _ ≤ ∏ _i ∈ s, Real.exp (u ^ 2 / 8) := by
      apply Finset.prod_le_prod
      · intro i _
        exact expect_nonneg P (fun ω => (Real.exp_pos _).le)
      · intro i _
        exact bernoulli_mgf P (A i) u
    _ = Real.exp (u ^ 2 * s.card / 8) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
      congr 1
      ring

/-- Weighted finite Cauchy–Schwarz, with no independence assumption. -/
theorem expect_mul_sq_le (P : PMF Ω) (f g : Ω → ℝ) :
    (expect P (fun ω => f ω * g ω)) ^ 2 ≤
      expect P (fun ω => (f ω) ^ 2) * expect P (fun ω => (g ω) ^ 2) := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun ω _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg (f ω)))
    (fun ω _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg (g ω)))
    (fun ω _ => by dsimp; nlinarith [sq_nonneg ((P ω).toReal)])

/-- Exponential Markov on a finite PMF. -/
theorem exp_markov (P : PMF Ω) (X : Ω → ℝ) {u t : ℝ} (hu : 0 < u) :
    probability P (fun ω => t ≤ X ω) ≤
      Real.exp (-u * t) * expect P (fun ω => Real.exp (u * X ω)) := by
  have hevent : (fun ω => t ≤ X ω) =
      (fun ω => Real.exp (u * t) ≤ Real.exp (u * X ω)) := by
    funext ω
    simp only [Real.exp_le_exp]
    apply propext
    constructor <;> intro h <;> nlinarith
  rw [hevent]
  have h := markov P (fun ω => (Real.exp_pos (u * X ω)).le)
    (Real.exp_pos (u * t))
  calc
    _ ≤ expect P (fun ω => Real.exp (u * X ω)) / Real.exp (u * t) := h
    _ = Real.exp (-u * t) * expect P (fun ω => Real.exp (u * X ω)) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]
      exact mul_comm _ _

/-- Combining two MGF estimates uses Cauchy–Schwarz, not independence. -/
theorem parity_mgf (P : PMF Ω) (S₀ S₁ : Ω → ℝ) (B₀ B₁ : ℝ)
    (h₀ : ∀ u : ℝ, expect P (fun ω => Real.exp (u * S₀ ω)) ≤
      Real.exp (u ^ 2 * B₀ / 8))
    (h₁ : ∀ u : ℝ, expect P (fun ω => Real.exp (u * S₁ ω)) ≤
      Real.exp (u ^ 2 * B₁ / 8)) (u : ℝ) :
    expect P (fun ω => Real.exp (u * (S₀ ω + S₁ ω))) ≤
      Real.exp (u ^ 2 * (B₀ + B₁) / 4) := by
  have hsq (S : Ω → ℝ) :
      expect P (fun ω => (Real.exp (u * S ω)) ^ 2) =
        expect P (fun ω => Real.exp ((2 * u) * S ω)) := by
    congr 1
    funext ω
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcs := expect_mul_sq_le P
    (fun ω => Real.exp (u * S₀ ω)) (fun ω => Real.exp (u * S₁ ω))
  have hprod : (fun ω => Real.exp (u * S₀ ω) * Real.exp (u * S₁ ω)) =
      (fun ω => Real.exp (u * (S₀ ω + S₁ ω))) := by
    funext ω
    rw [← Real.exp_add, mul_add]
  rw [hprod, hsq S₀, hsq S₁] at hcs
  have hbound := mul_le_mul (h₀ (2 * u)) (h₁ (2 * u))
    (expect_nonneg P (fun ω => (Real.exp_pos _).le)) (Real.exp_pos _).le
  have heq : Real.exp ((2 * u) ^ 2 * B₀ / 8) *
      Real.exp ((2 * u) ^ 2 * B₁ / 8) =
      (Real.exp (u ^ 2 * (B₀ + B₁) / 4)) ^ 2 := by
    simp only [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hbound
  have hpos := Real.exp_pos (u ^ 2 * (B₀ + B₁) / 4)
  nlinarith

/-- Sharp weak one-sided bounds from the all-real parity MGF estimate. -/
theorem subgaussian_tails (P : PMF Ω) (X : Ω → ℝ) {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t)
    (hmgf : ∀ u : ℝ, expect P (fun ω => Real.exp (u * X ω)) ≤
      Real.exp (u ^ 2 * B / 4)) :
    probability P (fun ω => t ≤ X ω) ≤ Real.exp (-t ^ 2 / B) ∧
    probability P (fun ω => X ω ≤ -t) ≤ Real.exp (-t ^ 2 / B) := by
  have upper (Y : Ω → ℝ)
      (hY : ∀ u : ℝ, expect P (fun ω => Real.exp (u * Y ω)) ≤
        Real.exp (u ^ 2 * B / 4)) :
      probability P (fun ω => t ≤ Y ω) ≤ Real.exp (-t ^ 2 / B) := by
    have hu : 0 < 2 * t / B := div_pos (mul_pos (by norm_num) ht) hB
    calc
      _ ≤ Real.exp (-(2 * t / B) * t) *
          expect P (fun ω => Real.exp ((2 * t / B) * Y ω)) := exp_markov P Y hu
      _ ≤ Real.exp (-(2 * t / B) * t) *
          Real.exp ((2 * t / B) ^ 2 * B / 4) :=
        mul_le_mul_of_nonneg_left (hY _) (Real.exp_pos _).le
      _ = Real.exp (-t ^ 2 / B) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
  refine ⟨upper X hmgf, ?_⟩
  have hneg : ∀ u : ℝ, expect P (fun ω => Real.exp (u * -X ω)) ≤
      Real.exp (u ^ 2 * B / 4) := by
    intro u
    simpa only [neg_mul, mul_neg, neg_sq] using hmgf (-u)
  have h := upper (fun ω => -X ω) hneg
  have hevent : (fun ω => t ≤ -X ω) = (fun ω => X ω ≤ -t) := by
    funext ω
    apply propext
    constructor <;> intro h <;> linarith
  rwa [hevent] at h


/-- Structural two-class concentration. The concrete application supplies the pointwise
component decomposition and each class's exact product-expectation identity. -/
theorem two_class_indicator_concentration {I : Type*} (P : PMF Ω) (X : Ω → ℝ)
    (c : ℝ) (s₀ s₁ : Finset I) (A : I → Ω → Prop)
    (hX : ∀ ω, X ω = c + (∑ i ∈ s₀, if A i ω then 1 else 0) +
      (∑ i ∈ s₁, if A i ω then 1 else 0))
    (hfactor₀ : ∀ u : ℝ,
      expect P (fun ω => ∏ i ∈ s₀,
        Real.exp (u * ((if A i ω then 1 else 0) - probability P (A i)))) =
      ∏ i ∈ s₀, expect P (fun ω =>
        Real.exp (u * ((if A i ω then 1 else 0) - probability P (A i)))))
    (hfactor₁ : ∀ u : ℝ,
      expect P (fun ω => ∏ i ∈ s₁,
        Real.exp (u * ((if A i ω then 1 else 0) - probability P (A i)))) =
      ∏ i ∈ s₁, expect P (fun ω =>
        Real.exp (u * ((if A i ω then 1 else 0) - probability P (A i)))))
    {M t : ℝ} (_hM : 0 < M) (hcard : (s₀.card : ℝ) + s₁.card ≤ M) (ht : 0 < t) :
    probability P (fun ω => t ≤ X ω - expect P X) ≤ Real.exp (-t ^ 2 / M) ∧
    probability P (fun ω => X ω - expect P X ≤ -t) ≤ Real.exp (-t ^ 2 / M) := by
  by_cases hzero : s₀.card + s₁.card = 0
  · have hs₀ : s₀ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hs₁ : s₁ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hc : X = fun _ => c := by
      funext ω
      simpa [hs₀, hs₁] using hX ω
    rw [hc, expect_const]
    simp only [sub_self, not_le.mpr ht,
      show ¬ (0 : ℝ) ≤ -t by linarith, probability_false]
    exact ⟨(Real.exp_pos _).le, (Real.exp_pos _).le⟩
  let S₀ := fun ω => ∑ i ∈ s₀, ((if A i ω then (1 : ℝ) else 0) - probability P (A i))
  let S₁ := fun ω => ∑ i ∈ s₁, ((if A i ω then (1 : ℝ) else 0) - probability P (A i))
  have hmean : expect P X = c + (∑ i ∈ s₀, probability P (A i)) +
      ∑ i ∈ s₁, probability P (A i) := by
    rw [show X = _ from funext hX, expect_add, expect_add, expect_const,
      expect_sum, expect_sum]
    rfl
  have hcenter : (fun ω => X ω - expect P X) = fun ω => S₀ ω + S₁ ω := by
    funext ω
    rw [hX, hmean]
    dsimp [S₀, S₁]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  have hB : (0 : ℝ) < (s₀.card : ℝ) + s₁.card := by
    exact_mod_cast (Nat.pos_of_ne_zero hzero)
  have hmgf := parity_mgf P S₀ S₁ (s₀.card : ℝ) (s₁.card : ℝ)
    (one_class_mgf P s₀ A hfactor₀) (one_class_mgf P s₁ A hfactor₁)
  have htail := subgaussian_tails P (fun ω => S₀ ω + S₁ ω) hB ht hmgf
  have hweak : Real.exp (-t ^ 2 / ((s₀.card : ℝ) + s₁.card)) ≤
      Real.exp (-t ^ 2 / M) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg t) hB hcard)
  constructor
  · rw [show (fun ω => t ≤ X ω - expect P X) =
        (fun ω => t ≤ S₀ ω + S₁ ω) from congrArg (fun f => fun ω => t ≤ f ω) hcenter]
    exact htail.1.trans hweak
  · rw [show (fun ω => X ω - expect P X ≤ -t) =
        (fun ω => S₀ ω + S₁ ω ≤ -t) from congrArg (fun f => fun ω => f ω ≤ -t) hcenter]
    exact htail.2.trans hweak

end RiffleLowerV2.Ascent
