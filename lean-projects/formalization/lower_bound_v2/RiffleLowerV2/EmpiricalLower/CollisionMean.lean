import RiffleLowerV2.Occupancy.Main
import RiffleLowerV2.Localization.Main

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Topology
open Filter
namespace RiffleLowerV2.EmpiricalLower
open TimeProfile

/-- The absolute marginal constant, equal to exp(-5)/4. -/
def coldMeanConstant : ℝ := (Real.exp (-1)/4) * (Real.exp (-2))^2

theorem coldMeanConstant_pos : 0 < coldMeanConstant := by
  unfold coldMeanConstant
  positivity

theorem coldMeanConstant_eq : coldMeanConstant = Real.exp (-5)/4 := by
  unfold coldMeanConstant
  calc
    _ = (Real.exp (-1)*Real.exp (-2)*Real.exp (-2))/4 := by ring
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; norm_num

/-- Uniform saturation bound, including arbitrarily small and large word means. -/
theorem cold_min_mean {N : ℕ} (hN : 1 ≤ N) {z u κ₀ : ℝ}
    (hκ₀ : 0 ≤ κ₀) (hz : z ≤ 2*κ₀)
    (hu : Real.exp (-2)*(N : ℝ)^z ≤ u) :
    (Real.exp (-2))^2*(N : ℝ)^(2*z-4*κ₀) ≤ min (u^2) 1 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hu0 : 0 ≤ Real.exp (-2)*(N : ℝ)^z := by positivity
  have hpow : (N : ℝ)^(2*z-4*κ₀) ≤ (N : ℝ)^(2*z) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hpow2 : (N : ℝ)^(2*z) = ((N : ℝ)^z)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    congr 1
    norm_num
    ring
  have hfirst : (Real.exp (-2))^2*(N : ℝ)^(2*z-4*κ₀) ≤ u^2 := by
    have hh := mul_le_mul_of_nonneg_left hpow (sq_nonneg (Real.exp (-2)))
    rw [hpow2] at hh
    nlinarith
  have hpowerOne : (N : ℝ)^(2*z-4*κ₀) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hNr (show 2*z-4*κ₀ ≤ 0 by linarith)
  have he : Real.exp (-2 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have he0 := (Real.exp_pos (-2 : ℝ)).le
  have hsecond : (Real.exp (-2))^2*(N : ℝ)^(2*z-4*κ₀) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hpowerOne (sq_nonneg (Real.exp (-2)))
    nlinarith
  exact le_min hfirst hsecond

/-- Geometry supplies a deterministic fixed positive selected-pile constant. -/
theorem geometry_selectedPiles {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {eta rho chi xi : ℝ} (P : BorelPartition k) (W : ColdWitnessData)
    (G : ColdGeometryData K P W) (hG : GeometrySpec cuts hN eta rho chi xi P W G) :
    selectedPiles cuts (coldFullFamily cuts hN P W G) (min xi (min chi (1/(k : ℝ)))) := by
  rcases hG with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩
  intro y hy j
  exact (le_div_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mp (hs y hy j)

/-- Exact finite mean lower bound from actual-model relative marginal estimates. -/
theorem cold_collision_mean_lower {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {eta rho chi xi D : ℝ} (heta : 0 < eta)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W)
    (hG : GeometrySpec cuts hN eta rho chi xi P W G)
    (hsmall : D*(N : ℝ)^(-1/100 : ℝ) ≤ 1/2)
    (hmarg : ∀ y ∈ coldFullFamily cuts hN P W G,
      |probability (fixedCountPMF cuts) (collisionEvent y) -
        poissonCollision ((N : ℝ)*wordMass cuts y)| ≤
      D*(N : ℝ)^(-1/100 : ℝ)*poissonCollision ((N : ℝ)*wordMass cuts y)) :
    coldMeanConstant*(N : ℝ)^(geometryG cuts hN P W G-4*kappa0 eta) ≤
      expect (fixedCountPMF cuts) (collisionCount (coldFullFamily cuts hN P W G)) := by
  rcases hG with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hz, hY, hmu, _⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ₀ : 0 ≤ kappa0 eta := by unfold kappa0 kappa; positivity
  have hterm (y : Word k K) (hy : y ∈ coldFullFamily cuts hN P W G) :
      coldMeanConstant*(N : ℝ)^(2*geometryZ cuts hN P W G-4*kappa0 eta) ≤
        probability (fixedCountPMF cuts) (collisionEvent y) := by
    have hu := (hmu y hy).1.le
    have hu0 : 0 ≤ (N : ℝ)*wordMass cuts y := (by positivity :
      0 < Real.exp (-2)*(N : ℝ)^(geometryZ cuts hN P W G)).le.trans hu
    have hmin := cold_min_mean (by omega : 1 ≤ N) hκ₀ hz hu
    have hf := Occupancy.poissonCollision_lower_min _ hu0
    have hf0 : 0 ≤ poissonCollision ((N : ℝ)*wordMass cuts y) := by
      have := mul_nonneg (by positivity : 0 ≤ Real.exp (-1)/2)
        (le_min (sq_nonneg ((N : ℝ)*wordMass cuts y)) zero_le_one)
      linarith
    have herr := (abs_le.mp (hmarg y hy)).1
    have hhalf := mul_le_mul_of_nonneg_right hsmall hf0
    have hmin' := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ Real.exp (-1)/2)
    unfold coldMeanConstant
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  have hexpect : expect (fixedCountPMF cuts) (collisionCount (coldFullFamily cuts hN P W G)) =
      ∑ y ∈ coldFullFamily cuts hN P W G, probability (fixedCountPMF cuts) (collisionEvent y) :=
    Occupancy.expect_eventCount _ _ _
  rw [hexpect]
  calc
    _ = (coldFullFamily cuts hN P W G).card *
        (coldMeanConstant*(N : ℝ)^(2*geometryZ cuts hN P W G-4*kappa0 eta)) := by
      rw [hY, mul_left_comm, ← Real.rpow_add hNp]
      congr 2
      unfold geometryG
      ring
    _ = ∑ y ∈ coldFullFamily cuts hN P W G,
        coldMeanConstant*(N : ℝ)^(2*geometryZ cuts hN P W G-4*kappa0 eta) := by simp
    _ ≤ _ := hsum

/-- The fixed positive slack is uniform over every finite witness. -/
theorem cold_exponent_slack {eta g h : ℝ}
    (hgap : kappa eta/2 ≤ g-h/2) :
    h/2+kappa eta/3+19*kappa eta/150 ≤ g-4*kappa0 eta := by
  have hκ₀ : kappa0 eta ≤ kappa eta/100 := min_le_left _ _
  linarith

/-- Uniform numerical thresholds, fixed before all varying exponents and geometry. -/
theorem exists_cold_mean_threshold (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      2/coldMeanConstant ≤ (N : ℝ)^(19*kappa eta/150) ∧
      2 ≤ (N : ℝ)^(kappa eta/12) := by
  have hκ : 0 < kappa eta := by unfold kappa; positivity
  obtain ⟨N1, hN1, h1⟩ := Localization.exists_rpow_threshold
    (19*kappa eta/150) (2/coldMeanConstant) (by positivity)
  obtain ⟨N2, _, h2⟩ := Localization.exists_rpow_threshold (kappa eta/12) 2 (by positivity)
  exact ⟨max N1 N2, hN1.trans (le_max_left _ _), fun N hN =>
    ⟨h1 N ((le_max_left _ _).trans hN), h2 N ((le_max_right _ _).trans hN)⟩⟩

/-- Absorb all fixed constants with the exact slack; the exponents may vary with the cuts. -/
theorem cold_mean_dominates {N : ℕ} (hN : 1 ≤ N) {eta M h g E : ℝ}
    (_heta : 0 < eta) (hM : 0 ≤ M) (hMupper : M ≤ 2*(N : ℝ)^h)
    (hgap : kappa eta/2 ≤ g-h/2)
    (hlarge : 2/coldMeanConstant ≤ (N : ℝ)^(19*kappa eta/150))
    (hmean : coldMeanConstant*(N : ℝ)^(g-4*kappa0 eta) ≤ E) :
    Real.sqrt M*(N : ℝ)^(kappa eta/3) ≤ E := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hconst : 2 ≤ coldMeanConstant*(N : ℝ)^(19*kappa eta/150) := by
    exact (div_le_iff₀ coldMeanConstant_pos).mp hlarge |>.trans_eq (mul_comm _ _)
  have hsqrt : Real.sqrt M ≤ 2*(N : ℝ)^(h/2) := by
    have hpow : ((N : ℝ)^(h/2))^2 = (N : ℝ)^h := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      congr 1
      norm_num
    have hsq := Real.sq_sqrt hM
    have hs0 := Real.sqrt_nonneg M
    have hp0 := Real.rpow_pos_of_pos hNp (h/2)
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hNr (cold_exponent_slack hgap)
  have hpow' := mul_le_mul_of_nonneg_left hpow coldMeanConstant_pos.le
  rw [Real.rpow_add hNp, Real.rpow_add hNp] at hpow'
  have hx := mul_le_mul_of_nonneg_left hconst
    (show 0 ≤ (N : ℝ)^(h/2)*(N : ℝ)^(kappa eta/3) by positivity)
  have hs := mul_le_mul_of_nonneg_right hsqrt
    (Real.rpow_nonneg hNp.le (kappa eta/3))
  nlinarith

end RiffleLowerV2.EmpiricalLower
