import RiffleUpperV2.Localization.Scalars

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Localization

/-- Elementary square-sum bound used for the unconditional small-block estimate. -/
theorem density_le_square_total {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) : ∑ i ∈ s, p i ^ 2 ≤ (∑ i ∈ s, p i)^2 := by
  simpa using Finset.sum_sq_le_sq_sum_of_nonneg hp

/-- The probability bound p≤1 turns density into expected edge count. -/
theorem density_le_total {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) : ∑ i ∈ s, p i^2 ≤ ∑ i ∈ s, p i := by
  apply Finset.sum_le_sum
  intro i hi
  exact sq_le (hp i hi).1 (hp i hi).2

theorem smallDensity_of_expected_edges {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    {μ tail : ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hexpect : ∑ i ∈ s, p i ≤ μ^2 * tail / 2) :
    ∑ i ∈ s, p i^2 ≤ μ^4 * tail^2 / 4 := by
  have hsum : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg hp
  calc
    _ ≤ (∑ i ∈ s, p i)^2 := density_le_square_total s p hp
    _ ≤ (μ^2*tail/2)^2 := pow_le_pow_left₀ hsum hexpect 2
    _ = _ := by ring

/-- This is the direct internal-offset argument: only one atom factor is paid.
Its two finite-sum premises are supplied by conditioning on the internal history. -/
theorem largeDensity_of_atoms {ι : Type*} (s : Finset ι) (p a b : ι → ℝ)
    {A E failure : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hsplit : ∀ i ∈ s, p i = a i + b i)
    (hatom : ∀ i ∈ s, a i ≤ A*E)
    (htotal : ∑ i ∈ s, a i ≤ E) (hfailure : ∑ i ∈ s, b i ≤ failure) :
    ∑ i ∈ s, p i^2 ≤ A*E^2 + 2*failure := by
  have hdifference (i : ι) (hi : i ∈ s) : p i^2 ≤ a i^2 + 2*b i := by
    have hpi := hp i hi
    have hai := ha i hi
    have hbi := hb i hi
    have hsplit_i := hsplit i hi
    have hai1 : a i ≤ 1 := by linarith
    nlinarith
  have hsq : ∑ i ∈ s, a i^2 ≤ A*E^2 := by
    calc
      _ ≤ ∑ i ∈ s, (A*E)*a i := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [mul_le_mul_of_nonneg_right (hatom i hi) (ha i hi)]
      _ = (A*E) * ∑ i ∈ s, a i := (Finset.mul_sum _ _ _).symm
      _ ≤ (A*E)*E := mul_le_mul_of_nonneg_left htotal (mul_nonneg hA hE)
      _ = A*E^2 := by ring
  calc
    _ ≤ ∑ i ∈ s, (a i^2 + 2*b i) := Finset.sum_le_sum hdifference
    _ = (∑ i ∈ s, a i^2) + 2*(∑ i ∈ s, b i) := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ A*E^2 + 2*failure := by linarith

theorem terminalDensity_of_expected_count {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    {μ : ℝ} (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hexpect : ∑ i ∈ s, p i ≤ μ) : ∑ i ∈ s, p i^2 ≤ μ :=
  (density_le_total s p hp).trans hexpect

end RiffleUpperV2.Localization
