import RiffleUpperV2.GraphOverlap.FiniteProbability
import RiffleLowerV2.Factorial.Exact
import Mathlib.Data.Nat.Choose.Bounds

/-! Exact occupancy moments and sampling-without-replacement comparison.
The ratio proof is an additive public port of the private theorem of the same
name in lower_bound_v2/Thinning/Compat/HypergeometricConcentration.lean.
Its source and destination hashes are recorded in audit/U01. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.GraphOverlap
open TimeProfile RiffleLowerV2 RiffleLowerV2.Factorial

theorem descFactorial_ratio_le_pow {N m : ℕ} (hm : m ≤ N) (r : ℕ) :
    (m.descFactorial r : ℝ) / (N.descFactorial r : ℝ) ≤ ((m : ℝ) / N) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      by_cases hrm : r < m
      · have hrN : r < N := lt_of_lt_of_le hrm hm
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le r) hrN)
        have hfactor : ((m - r : ℕ) : ℝ) / ((N - r : ℕ) : ℝ) ≤ (m : ℝ) / N := by
          rw [Nat.cast_sub (Nat.le_of_lt hrm), Nat.cast_sub (Nat.le_of_lt hrN)]
          have hrNr : (r : ℝ) < N := by exact_mod_cast hrN
          have hmr : (m : ℝ) ≤ N := by exact_mod_cast hm
          apply (div_le_div_iff₀ (sub_pos.mpr hrNr) hNpos).2
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) r) (sub_nonneg.mpr hmr)]
        rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul,
          mul_div_mul_comm, pow_succ']
        exact mul_le_mul hfactor ih (by positivity) (by positivity)
      · have hz : m.descFactorial (r + 1) = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        rw [hz, Nat.cast_zero, zero_div]
        positivity


theorem wordFactorialMoment {k N K : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (q : ℕ) (hq : q ≤ N) :
    RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) q) =
      falling N q * ∏ j, falling (cuts.count j (w.get j)) q / falling N q := by
  have h := exactJointFactorial cuts (fun _ : Fin 1 => w) (fun _ => q)
    (fun _ _ _ => Subsingleton.elim _ _) (by simpa using hq)
  change RiffleLowerV2.expect (fixedCountPMF cuts)
    (fun ω => ∏ i : Fin 1, falling (wordCount w ω) q) = _ at h
  simp only [Fin.prod_univ_one, exactFactorial, Fin.sum_univ_one,
    requestedCount] at h
  have hp (j : Fin K) : (∏ a : Fin k, falling (cuts.count j a)
      (if w.get j = a then q else 0)) = falling (cuts.count j (w.get j)) q := by
    rw [Finset.prod_eq_single (w.get j)]
    · simp
    · intro a _ ha
      simp [Ne.symm ha, falling]
    · simp
  simp only [Fin.sum_univ_one, hp] at h
  exact h

theorem wordMass_eq_prod {k N K : ℕ} (cuts : Cuts k N K) (w : Word k K) :
    wordMass cuts w = ∏ j, (cuts.count j (w.get j) : ℝ) / N := rfl

theorem wordMass_nonneg {k N K : ℕ} (cuts : Cuts k N K) (w : Word k K) :
    0 ≤ wordMass cuts w := by
  rw [wordMass_eq_prod]
  exact Finset.prod_nonneg (fun _ _ => by positivity)

theorem count_le_population {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) (a : Fin k) :
    cuts.count j a ≤ N := by
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans_eq (cuts.sum_count j)

theorem wordFactorialMoment_le {k N K : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (q : ℕ) (hq : q ≤ N) :
    RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) q) ≤
      falling N q * wordMass cuts w ^ q := by
  rw [wordFactorialMoment cuts w q hq, wordMass_eq_prod, ← Finset.prod_pow]
  apply mul_le_mul_of_nonneg_left _ (falling_nonneg _ _)
  apply Finset.prod_le_prod (fun _ _ => by apply div_nonneg <;> exact falling_nonneg _ _)
  intro j _
  exact descFactorial_ratio_le_pow (count_le_population cuts j (w.get j)) q

theorem wordBinomialMoment_le {k N K : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (q : ℕ) (hq : q ≤ N) :
    RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => ((wordCount w ω).choose q : ℝ)) ≤
      (N.choose q : ℝ) * wordMass cuts w ^ q := by
  simp_rw [choose_eq_falling_div]
  rw [expect_div]
  have h := div_le_div_of_nonneg_right (wordFactorialMoment_le cuts w q hq)
    (Nat.cast_nonneg q.factorial)
  calc
    _ ≤ (falling N q * wordMass cuts w ^ q) / q.factorial := h
    _ = _ := by ring

theorem wordMass_sum {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) :
    (∑ w : Word k K, wordMass cuts w) = 1 := by
  have hs := (Equiv.vectorEquivFin (Fin k) K).sum_comp
    (fun w : Fin K → Fin k => ∏ j, (cuts.count j (w j) : ℝ)/N)
  change (∑ w : Word k K, ∏ j, (cuts.count j (w.get j) : ℝ)/N) = _
  change (∑ w : Word k K, ∏ j, (cuts.count j (w.get j) : ℝ)/N) = _ at hs
  rw [hs, ← Fintype.prod_sum (fun (j : Fin K) (a : Fin k) => (cuts.count j a : ℝ)/N)]
  have hc (j : Fin K) : (∑ a : Fin k, (cuts.count j a : ℝ)/N) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, cuts.sum_count]
    exact div_self (by exact_mod_cast hN.ne')
  simp only [hc, Finset.prod_const_one]

/-- The maximal full-word mean from the actual cut profiles. -/
theorem wordMass_le_maximalMean_div {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (w : Word k K) : wordMass cuts w ≤ maximalMean cuts hN / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [maximalMean, mul_div_cancel_left₀ _ hNr.ne', wordMass_eq_prod]
  apply Finset.prod_le_prod (fun _ _ => by positivity)
  intro j _
  exact TimeProfile.prob_le_pileMax (cuts.profile hN j) (w.get j)

theorem wordCount_le_population {k N K : ℕ} {cuts : Cuts k N K}
    (w : Word k K) (ω : Sample cuts) : wordCount w ω ≤ N := by
  rw [wordCount_eq_card, Fintype.card_subtype]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- `q>N` is impossible, including populations zero and one. -/
theorem largestComponentTail_zero {k N K q : ℕ} (cuts : Cuts k N K) (hq : N < q) :
    RiffleLowerV2.probability (fixedCountPMF cuts) (fun ω => ∃ w : Word k K, q ≤ wordCount w ω) = 0 := by
  have hn (ω : Sample cuts) : ¬ ∃ w : Word k K, q ≤ wordCount w ω := by
    rintro ⟨w, hw⟩
    exact (not_le_of_gt hq) (hw.trans (wordCount_le_population w ω))
  simp [RiffleLowerV2.probability, hn, expect_const]

theorem largestComponentTail_sum {k N K q : ℕ} (cuts : Cuts k N K) (hq : q ≤ N) :
    RiffleLowerV2.probability (fixedCountPMF cuts) (fun ω => ∃ w : Word k K, q ≤ wordCount w ω) ≤
      (N.choose q : ℝ) * ∑ w : Word k K, wordMass cuts w ^ q := by
  have hpoint (ω : Sample cuts) :
      (if ∃ w : Word k K, q ≤ wordCount w ω then (1 : ℝ) else 0) ≤
        ∑ w : Word k K, ((wordCount w ω).choose q : ℝ) := by
    split_ifs with h
    · obtain ⟨w, hw⟩ := h
      have hp : (1 : ℝ) ≤ (wordCount w ω).choose q := by
        exact_mod_cast Nat.choose_pos hw
      exact hp.trans (Finset.single_le_sum (f := fun v : Word k K => ((wordCount v ω).choose q : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ w))
    · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  calc
    _ ≤ RiffleLowerV2.expect (fixedCountPMF cuts)
        (fun ω => ∑ w : Word k K, ((wordCount w ω).choose q : ℝ)) :=
      (by
        unfold RiffleLowerV2.probability
        apply expect_mono
        intro ω
        convert hpoint ω using 1
        split_ifs <;> rfl)
    _ = ∑ w : Word k K, RiffleLowerV2.expect (fixedCountPMF cuts)
        (fun ω => ((wordCount w ω).choose q : ℝ)) := expect_sum _ _ _
    _ ≤ ∑ w : Word k K, (N.choose q : ℝ) * wordMass cuts w ^ q :=
      Finset.sum_le_sum (fun w _ => wordBinomialMoment_le cuts w q hq)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem largestComponentTail {k N K q : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (hq : 2 ≤ q) (hqN : q ≤ N) :
    RiffleLowerV2.probability (fixedCountPMF cuts) (fun ω => ∃ w : Word k K, q ≤ wordCount w ω) ≤
      (N.choose q : ℝ) * (maximalMean cuts hN / N) ^ (q-1) := by
  apply (largestComponentTail_sum cuts hqN).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    (∑ w : Word k K, wordMass cuts w ^ q) ≤
        ∑ w : Word k K, wordMass cuts w * (maximalMean cuts hN/N)^(q-1) := by
      apply Finset.sum_le_sum
      intro w _
      have he : q = (q-1)+1 := by omega
      conv_lhs => rw [he, pow_succ']
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (wordMass_nonneg cuts w) (wordMass_le_maximalMean_div cuts hN w) _)
        (wordMass_nonneg cuts w)
    _ = _ := by rw [← Finset.sum_mul, wordMass_sum cuts hN, one_mul]

end RiffleUpperV2.GraphOverlap
