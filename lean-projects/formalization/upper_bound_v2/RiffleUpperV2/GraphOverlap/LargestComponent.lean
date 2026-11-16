import RiffleUpperV2.GraphOverlap.Components

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.GraphOverlap
open TimeProfile RiffleLowerV2 RiffleLowerV2.Factorial

theorem choose_mul_ratio_pow_le {N q : ℕ} (hN : 0 < N) (hq : 1 ≤ q)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    (N.choose q : ℝ) * (μ/N)^(q-1) ≤ N * μ^(q-1) / q.factorial := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp : (N : ℝ)^q = (N : ℝ)^(q-1) * N := by
    have hq' : q = (q-1)+1 := by omega
    conv_lhs => rw [hq', pow_succ]
  calc
    _ ≤ ((N : ℝ)^q/q.factorial) * (μ/N)^(q-1) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div q N) (by positivity)
    _ = _ := by rw [hp, div_pow]; field_simp

theorem maximalMean_nonneg {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) :
    0 ≤ maximalMean cuts hN := by
  unfold maximalMean
  apply mul_nonneg (Nat.cast_nonneg _)
  exact Finset.prod_nonneg (fun j _ => (pileMax_pos _).le)

theorem largestComponentTail_factorial {k N K q : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (hq : 2 ≤ q) :
    RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (fun ω => ∃ w : Word k K, q ≤ wordCount w ω) ≤
      N * (maximalMean cuts hN)^(q-1) / q.factorial := by
  by_cases hqN : q ≤ N
  · exact (largestComponentTail cuts hN hq hqN).trans
      (choose_mul_ratio_pow_le hN (by omega) (maximalMean_nonneg cuts hN))
  · rw [largestComponentTail_zero cuts (Nat.lt_of_not_ge hqN)]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (maximalMean_nonneg cuts hN) _)) (Nat.cast_nonneg _)

theorem boundedComponentTail {k N K B : ℕ} (cuts : Cuts k N K)
    (hN : 2 ≤ N) (hB : 2 ≤ B) {η A : ℝ}
    (hμ : maximalMean cuts (by omega) ≤ (N : ℝ)^(-η))
    (hexp : A+1 ≤ η*B) :
    RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (fun ω => ¬ BoundedComponents (shuffleEdges ω) B) ≤
      (N : ℝ)^(-A) / (B+1).factorial := by
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hevent : (fun ω : Sample cuts => ¬ BoundedComponents (shuffleEdges ω) B) =
      (fun ω => ∃ w : Word k K, B+1 ≤ wordCount w ω) := by
    funext ω
    exact propext (not_boundedComponents_shuffle ω)
  rw [hevent]
  apply (largestComponentTail_factorial cuts hNpos (show 2 ≤ B+1 by omega)).trans
  simp only [Nat.add_sub_cancel]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (N : ℝ) * maximalMean cuts hNpos ^ B ≤ (N : ℝ) * ((N : ℝ)^(-η))^B :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (maximalMean_nonneg cuts hNpos) hμ B) hNr.le
    _ = (N : ℝ)^(1 + (-η)*(B : ℝ)) := by
      rw [← Real.rpow_mul_natCast hNr.le, Real.rpow_add hNr, Real.rpow_one]
    _ ≤ (N : ℝ)^(-A) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

end RiffleUpperV2.GraphOverlap
