import RiffleUpperV2.Exploration.PrefixConcentration
import RiffleUpperV2.Hypergeometric.CylinderMean

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open Hypergeometric RiffleLowerV2.Thinning

/-- A stronger simultaneous event over deterministic allowed-digit cylinders. -/
def allCylinderEvent {k n K : ℕ} (cuts : Cuts k n K) (ξ : ℝ) (ω : Sample cuts) : Prop :=
  ∀ Ds : Fin K → Finset (Fin k),
    |(cylinderCount cuts Finset.univ Ds ω : ℝ) - cylinderMean cuts Finset.univ Ds| ≤
      (max (cylinderMean cuts Finset.univ Ds) ((n : ℝ)^ξ))^((2:ℝ)/3)/2

/-- Certified denominator four, with the stronger half-sized tolerance. -/
theorem half_twoThirds_exponent {μ M : ℝ} (hμ : 0 ≤ μ) (hM : 1 ≤ M) (hμM : μ ≤ M) :
    -((M^((2:ℝ)/3)/2)^2)/(4*(μ+M^((2:ℝ)/3)/2)) ≤ -M^((1:ℝ)/3)/24 := by
  have hp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have ha : M^((2:ℝ)/3) ≤ M := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM
      (by norm_num : (2:ℝ)/3 ≤ 1)
  have he : (M^((2:ℝ)/3))^2 = M*M^((1:ℝ)/3) := by
    calc
      _ = M^(((2:ℝ)/3)*2) := by rw [Real.rpow_mul hp.le]; norm_num
      _ = M^((1:ℝ)+(1:ℝ)/3) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hp, Real.rpow_one]
  have hd : 0 < 4*(μ+M^((2:ℝ)/3)/2) := by positivity
  have h₁ := mul_le_mul_of_nonneg_left ha (Real.rpow_nonneg hp.le ((1:ℝ)/3))
  have h₂ := mul_le_mul_of_nonneg_left hμM (Real.rpow_nonneg hp.le ((1:ℝ)/3))
  apply (div_le_div_iff₀ hd (by norm_num : (0:ℝ)<24)).2
  nlinarith [he]

theorem cylinder_half_concentration {k n K : ℕ} (cuts : Cuts k n K)
    (hn : 0 < n) {ξ : ℝ} (hξ : 0 ≤ ξ) (Ds : Fin K → Finset (Fin k)) :
    probability (fixedCountPMF cuts) (fun ω =>
      (max (cylinderMean cuts Finset.univ Ds) ((n : ℝ)^ξ))^((2:ℝ)/3)/2 <
      |(cylinderCount cuts Finset.univ Ds ω : ℝ) - cylinderMean cuts Finset.univ Ds|) ≤
      2 * Real.exp (-(n : ℝ)^(ξ/3)/24) := by
  let μ := cylinderMean cuts Finset.univ Ds
  let M := max μ ((n : ℝ)^ξ)
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hb : 1 ≤ (n : ℝ)^ξ := Real.one_le_rpow (by exact_mod_cast hn) hξ
  have hM : 1 ≤ M := hb.trans (le_max_right _ _)
  have hμ : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg _) (cylinderMass_bounds cuts Ds).1
  have ht : 0 < M^((2:ℝ)/3)/2 := by positivity
  have htail := (anchorCylinderTail cuts Finset.univ Ds ht).1
  calc
    _ ≤ probability (fixedCountPMF cuts) (fun ω => M^((2:ℝ)/3)/2 ≤
        |(cylinderCount cuts Finset.univ Ds ω : ℝ)-μ|) := probability_mono _ (fun _ h => h.le)
    _ ≤ 2 * Real.exp (-((M^((2:ℝ)/3)/2)^2)/(4*(μ+M^((2:ℝ)/3)/2))) := htail
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      apply (half_twoThirds_exponent hμ hM (le_max_left _ _)).trans
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg hn0 ξ) (le_max_right μ ((n:ℝ)^ξ))
        (by norm_num : (0:ℝ)≤1/3)
      rw [← Real.rpow_mul hn0] at hh
      have he : ξ*((1:ℝ)/3) = ξ/3 := by ring
      rw [he] at hh
      linarith

/-- Exact finite union cost; n and every digit-set restriction remain deterministic. -/
theorem allCylinderFailure {k n K : ℕ} (cuts : Cuts k n K) (hn : 0 < n)
    {ξ : ℝ} (hξ : 0 ≤ ξ) :
    probability (fixedCountPMF cuts) (fun ω => ¬ allCylinderEvent cuts ξ ω) ≤
      2 * ((2:ℝ)^k)^K * Real.exp (-(n : ℝ)^(ξ/3)/24) := by
  have hm : probability (fixedCountPMF cuts) (fun ω => ¬ allCylinderEvent cuts ξ ω) ≤
      probability (fixedCountPMF cuts) (fun ω => ∃ Ds : Fin K → Finset (Fin k),
        (max (cylinderMean cuts Finset.univ Ds) ((n : ℝ)^ξ))^((2:ℝ)/3)/2 <
        |(cylinderCount cuts Finset.univ Ds ω : ℝ) - cylinderMean cuts Finset.univ Ds|) := by
    apply probability_mono
    intro ω h
    simpa only [allCylinderEvent, not_forall, not_le] using h
  apply hm.trans
  apply (probability_iUnion_le (fixedCountPMF cuts) _).trans
  calc
    _ ≤ ∑ _ : Fin K → Finset (Fin k), 2*Real.exp (-(n : ℝ)^(ξ/3)/24) :=
      Finset.sum_le_sum (fun Ds _ => cylinder_half_concentration cuts hn hξ Ds)
    _ = _ := by simp [Fintype.card_finset]; ring

/-- Reusable deterministic consequence when the cylinder mean is bounded by m. -/
theorem allCylinderEvent_bound {k n K : ℕ} (cuts : Cuts k n K) {ξ m : ℝ}
    {ω : Sample cuts} (h : allCylinderEvent cuts ξ ω) (Ds : Fin K → Finset (Fin k))
    (hb : (n : ℝ)^ξ ≤ m) (hm : cylinderMean cuts Finset.univ Ds ≤ m) :
    |(cylinderCount cuts Finset.univ Ds ω : ℝ) - cylinderMean cuts Finset.univ Ds| ≤
      m^((2:ℝ)/3)/2 := by
  apply (h Ds).trans
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Real.rpow_le_rpow (le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) ξ) (le_max_right _ _))
    (max_le hm hb) (by norm_num)

end RiffleUpperV2.Exploration
