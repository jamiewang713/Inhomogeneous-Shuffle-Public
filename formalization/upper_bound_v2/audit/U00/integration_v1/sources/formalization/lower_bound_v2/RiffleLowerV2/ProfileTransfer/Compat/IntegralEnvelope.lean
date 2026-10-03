/- Provenance: fresh source port of ../time_profile/RiffleTimeProfile/IntegralEnvelope.lean. Namespace and imports adapted only. -/
import RiffleTimeProfile.Base

/-!
C01 and C02 of the frozen analytic continuation: probability fibers and
one-sided bounds for totalized integrals with arbitrary time dependence.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace RiffleLowerV2.ProfileTransfer.Compat
open TimeProfile

theorem BorelPartition.measurableSet_cell {k : ℕ} (P : BorelPartition k)
    (i : Fin P.cellCount) : MeasurableSet (P.cell i) := by
  change MeasurableSet (P.classify ⁻¹' {i})
  exact P.measurable_classify (measurableSet_singleton i)

theorem BorelPartition.cell_mass_bounds {k : ℕ} (P : BorelPartition k)
    (nu : ProbabilityMeasure (Simplex k)) (i : Fin P.cellCount) :
    0 ≤ ((nu : Measure (Simplex k)) (P.cell i)).toReal ∧
      ((nu : Measure (Simplex k)) (P.cell i)).toReal ≤ 1 := by
  exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

theorem BorelPartition.sum_cell_mass {k : ℕ} (P : BorelPartition k)
    (nu : ProbabilityMeasure (Simplex k)) :
    ∑ i, ((nu : Measure (Simplex k)) (P.cell i)).toReal = 1 := by
  classical
  have h := sum_measureReal_preimage_singleton
    (μ := (nu : Measure (Simplex k))) (f := P.classify) Finset.univ
    (fun i _ => BorelPartition.measurableSet_cell P i)
  change ∑ i, (nu : Measure (Simplex k)).real (P.classify ⁻¹' {i}) = 1
  simpa only [Finset.coe_univ, Set.preimage_univ, probReal_univ] using h

theorem cellMass_bounds {k : ℕ} (mu : TimeLaw k) (P : BorelPartition k)
    (i : Fin P.cellCount) (t : ℝ) :
    0 ≤ cellMass mu P i t ∧ cellMass mu P i t ≤ 1 :=
  BorelPartition.cell_mass_bounds P (mu t) i

theorem sum_cellMass {k : ℕ} (mu : TimeLaw k) (P : BorelPartition k) (t : ℝ) :
    ∑ i, cellMass mu P i t = 1 :=
  BorelPartition.sum_cell_mass P (mu t)

theorem probability_integral_bounds {k : ℕ} (nu : ProbabilityMeasure (Simplex k))
    (f : Simplex k → ℝ) {M : ℝ} (_hM : 0 ≤ M)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M) :
    0 ≤ ∫ p, f p ∂(nu : Measure (Simplex k)) ∧
      ∫ p, f p ∂(nu : Measure (Simplex k)) ≤ M := by
  refine ⟨integral_nonneg (fun p => (hf p).1), ?_⟩
  have h := integral_mono_of_nonneg
    (ae_of_all (nu : Measure (Simplex k)) (fun p => (hf p).1))
    (integrable_const M)
    (ae_of_all (nu : Measure (Simplex k)) (fun p => (hf p).2))
  simpa using h

theorem probability_integral_le_cell_sum {k : ℕ} (P : BorelPartition k)
    (nu : ProbabilityMeasure (Simplex k)) (f : Simplex k → ℝ) {M omega : ℝ}
    (_hM : 0 ≤ M) (_homega : 0 ≤ omega)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M)
    (herr : ∀ p, |f p - f (P.rep (P.classify p))| ≤ omega) :
    ∫ p, f p ∂(nu : Measure (Simplex k)) ≤
      omega + ∑ i, f (P.rep i) * ((nu : Measure (Simplex k)) (P.cell i)).toReal := by
  classical
  let g : Simplex k → ℝ := fun p =>
    ∑ i, (P.cell i).indicator (fun _ => f (P.rep i)) p
  have hgpoint (p : Simplex k) : g p = f (P.rep (P.classify p)) := by
    dsimp only [g]
    rw [Finset.sum_eq_single (P.classify p)]
    · simp [BorelPartition.cell]
    · intro i _ hi
      simp [BorelPartition.cell, Ne.symm hi]
    · simp
  have hgi (i : Fin P.cellCount) :
      Integrable ((P.cell i).indicator (fun _ => f (P.rep i)))
        (nu : Measure (Simplex k)) :=
    (integrable_const _).indicator (BorelPartition.measurableSet_cell P i)
  have hg : Integrable g (nu : Measure (Simplex k)) :=
    integrable_finsetSum Finset.univ (fun i _ => hgi i)
  have hgintegral : ∫ p, g p ∂(nu : Measure (Simplex k)) =
      ∑ i, f (P.rep i) * ((nu : Measure (Simplex k)) (P.cell i)).toReal := by
    dsimp only [g]
    rw [integral_finsetSum Finset.univ (fun i _ => hgi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator_const _ (BorelPartition.measurableSet_cell P i)]
    simp [measureReal_def, mul_comm]
  calc
    ∫ p, f p ∂(nu : Measure (Simplex k)) ≤
        ∫ p, omega + g p ∂(nu : Measure (Simplex k)) := by
      apply integral_mono_of_nonneg
        (ae_of_all _ (fun p => (hf p).1)) ((integrable_const omega).add hg)
      apply ae_of_all
      intro p
      change f p ≤ omega + g p
      rw [hgpoint]
      have hp := (abs_le.mp (herr p)).2
      linarith
    _ = omega + ∑ i, f (P.rep i) *
        ((nu : Measure (Simplex k)) (P.cell i)).toReal := by
      rw [integral_add (integrable_const omega) hg, hgintegral]
      simp

theorem finite_integral_envelope {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (nu : Measure Ω) [IsFiniteMeasure nu] (h : ι → Ω → ℝ) (r : ι → ℝ)
    (F : Ω → ℝ) {M omega : ℝ} (_hM : 0 ≤ M) (_homega : 0 ≤ omega)
    (hh : ∀ i t, 0 ≤ h i t) (hsum : ∀ t, ∑ i, h i t = 1)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ M) (hF : ∀ t, 0 ≤ F t)
    (hbound : ∀ t, F t ≤ omega + ∑ i, r i * h i t) :
    ∫ t, F t ∂nu ≤ (M + omega) * nu.real univ -
      ∑ i, (M - r i) * ∫ t, h i t ∂nu := by
  classical
  let G : Finset ι := Finset.univ.filter fun i => Integrable (h i) nu
  have hGi (i : ι) (hi : i ∈ G) : Integrable (fun t => (M - r i) * h i t) nu :=
    (Finset.mem_filter.mp hi).2.const_mul (M - r i)
  have hGs : Integrable (fun t => ∑ i ∈ G, (M - r i) * h i t) nu :=
    integrable_finsetSum G hGi
  have hmajorant (t : Ω) : F t ≤ (M + omega) - ∑ i ∈ G, (M - r i) * h i t := by
    have hall : ∑ i, (M - r i) * h i t = M - ∑ i, r i * h i t := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum t]
      ring
    have hsub : ∑ i ∈ G, (M - r i) * h i t ≤ ∑ i, (M - r i) * h i t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
      intro i _ _
      exact mul_nonneg (sub_nonneg.mpr (hr i).2) (hh i t)
    linarith [hbound t]
  have hint := integral_mono_of_nonneg (ae_of_all nu hF)
    ((integrable_const (M + omega)).sub hGs) (ae_of_all nu hmajorant)
  change (∫ t, F t ∂nu) ≤ ∫ t, (M + omega) - ∑ i ∈ G, (M - r i) * h i t ∂nu at hint
  rw [integral_sub (integrable_const (M + omega)) hGs,
    integral_const, integral_finsetSum G hGi] at hint
  simp_rw [integral_const_mul] at hint
  have hsum_integrals :
      ∑ i ∈ G, (M - r i) * ∫ t, h i t ∂nu =
        ∑ i, (M - r i) * ∫ t, h i t ∂nu := by
    apply Finset.sum_subset (Finset.subset_univ G)
    intro i _ hi
    have hni : ¬ Integrable (h i) nu := by
      simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    rw [integral_undef hni, mul_zero]
  rw [hsum_integrals] at hint
  simpa only [smul_eq_mul, mul_comm (nu.real univ) (M + omega)] using hint

theorem finite_integral_envelope_of_counts {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (nu : Measure Ω) [IsFiniteMeasure nu]
    (h : ι → Ω → ℝ) (r : ι → ℝ) (F : Ω → ℝ) {M omega : ℝ}
    (hM : 0 ≤ M) (homega : 0 ≤ omega)
    (hh : ∀ i t, 0 ≤ h i t) (hsum : ∀ t, ∑ i, h i t = 1)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ M) (hF : ∀ t, 0 ≤ F t)
    (hbound : ∀ t, F t ≤ omega + ∑ i, r i * h i t)
    (c : ι → ℝ) {d e : ℝ} (hd : 0 ≤ d)
    (hc : ∀ i, |c i - ∫ t, h i t ∂nu| ≤ d)
    (hmass : nu.real univ - ∑ i, c i ≤ e) :
    ∫ t, F t ∂nu ≤ ∑ i, r i * c i + omega * nu.real univ +
      M * (e + (Fintype.card ι : ℝ) * d) := by
  classical
  have hterm (i : ι) : (M - r i) * (c i - ∫ t, h i t ∂nu) ≤ M * d := by
    calc
      (M - r i) * (c i - ∫ t, h i t ∂nu) ≤ (M - r i) * d :=
        mul_le_mul_of_nonneg_left (abs_le.mp (hc i)).2 (sub_nonneg.mpr (hr i).2)
      _ ≤ M * d := mul_le_mul_of_nonneg_right (by linarith [(hr i).1]) hd
  have hterms : ∑ i, (M - r i) * (c i - ∫ t, h i t ∂nu) ≤
      (Fintype.card ι : ℝ) * (M * d) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hterm i)
  have hmass' := mul_le_mul_of_nonneg_left hmass hM
  calc
    ∫ t, F t ∂nu ≤ (M + omega) * nu.real univ -
        ∑ i, (M - r i) * ∫ t, h i t ∂nu :=
      finite_integral_envelope nu h r F hM homega hh hsum hr hF hbound
    _ = ∑ i, r i * c i + omega * nu.real univ +
        M * (nu.real univ - ∑ i, c i) +
        ∑ i, (M - r i) * (c i - ∫ t, h i t ∂nu) := by
      simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ ≤ ∑ i, r i * c i + omega * nu.real univ +
        M * (e + (Fintype.card ι : ℝ) * d) := by
      nlinarith

theorem interval_integral_envelope_of_counts {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (h : ι → ℝ → ℝ) (r : ι → ℝ) (F : ℝ → ℝ)
    {M omega : ℝ} (hM : 0 ≤ M) (homega : 0 ≤ omega)
    (hh : ∀ i t, 0 ≤ h i t) (hsum : ∀ t, ∑ i, h i t = 1)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ M) (hF : ∀ t, 0 ≤ F t)
    (hbound : ∀ t, F t ≤ omega + ∑ i, r i * h i t)
    (c : ι → ℝ) {d e : ℝ} (hd : 0 ≤ d)
    (hc : ∀ i, |c i - ∫ t in a..b, h i t| ≤ d)
    (hmass : (b - a) - ∑ i, c i ≤ e) :
    ∫ t in a..b, F t ≤ ∑ i, r i * c i + omega * (b - a) +
      M * (e + (Fintype.card ι : ℝ) * d) := by
  have hcounts (i : ι) : |c i - ∫ t, h i t ∂(volume.restrict (Ioc a b))| ≤ d := by
    simpa only [intervalIntegral.integral_of_le hab] using hc i
  have hlength : (volume.restrict (Ioc a b)).real univ - ∑ i, c i ≤ e := by
    simpa only [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hab] using hmass
  have hresult := finite_integral_envelope_of_counts (volume.restrict (Ioc a b))
    h r F hM homega hh hsum hr hF hbound c hd hcounts hlength
  simpa only [intervalIntegral.integral_of_le hab,
    measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hab] using hresult

end RiffleLowerV2.ProfileTransfer.Compat
