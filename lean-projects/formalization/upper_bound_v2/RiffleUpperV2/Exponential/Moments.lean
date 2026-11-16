import RiffleUpperV2.Exponential.Stopping

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exponential
open RiffleLowerV2.Thinning

variable {Ω H : Type*} [Fintype Ω] [Fintype H]

/-- The stopped remainder has the uniform conditional bound on every history.
The original remainder premise includes time zero. -/
theorem stoppedTail (P : PMF Ω) (h : ℕ → Ω → H) (X : ℕ → Ω → ℕ)
    (B : ℕ → Ω → Prop) (m : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (href : Refining h m) (hunit : ∀ ω, UnitIncrements (fun i => X i ω) m)
    (hB : ∀ i ≤ m, HistoryMeasurable (h i) (B i))
    (htail : ∀ i < m, ∀ a, B i a → 0 < probability P (fun ω => h i ω = h i a) →
      conditionalExpect P (fun ω => (X m ω - X i ω : ℕ))
        (fun ω => h i ω = h i a) ≤ γ)
    (i : ℕ) (hi : i ≤ m) (a : Ω) :
    conditionalExpect P
      (fun ω => (stoppedProcess X B m ω - stoppedProcess X B i ω : ℕ))
      (fun ω => h i ω = h i a) ≤ γ := by
  by_cases hz : probability P (fun ω => h i ω = h i a) = 0
  · simp [RiffleLowerV2.conditionalExpect, hz, hγ]
  have hp : 0 < probability P (fun ω => h i ω = h i a) :=
    lt_of_le_of_ne (probability_nonneg _ _) (Ne.symm hz)
  by_cases him : i = m
  · subst i
    simpa [RiffleLowerV2.conditionalExpect, RiffleLowerV2.expect] using hγ
  have him' : i < m := lt_of_le_of_ne hi him
  by_cases hb : goodPrefix B i a
  · apply le_trans (conditionalExpect_mono_on P _ (fun ω hω => ?_))
      (htail i him' a (hb i le_rfl) hp)
    have hba := goodPrefix_adapted href B hB hi ω a hω
    have hbw : goodPrefix B i ω := hba ▸ hb
    exact_mod_cast (by simpa only [hbw, if_true] using stoppedProcess_tail_le B hunit hi ω)
  · have he : conditionalExpect P
        (fun ω => (stoppedProcess X B m ω - stoppedProcess X B i ω : ℕ))
        (fun ω => h i ω = h i a) = 0 := by
      apply conditionalExpect_zero_on
      intro ω hω
      have hba := goodPrefix_adapted href B hB hi ω a hω
      have hbw : ¬ goodPrefix B i ω := by simpa only [hba] using hb
      have hn : stoppedProcess X B m ω - stoppedProcess X B i ω = 0 := by
        have ht := stoppedProcess_tail_le B hunit hi ω
        simpa only [hbw, if_false, Nat.le_zero] using ht
      simp only [hn, Nat.cast_zero]
    rw [he]
    exact hγ

/-- The conditional-binomial induction is proved against every nonnegative weight
measurable at the starting history. Its summands use weights measurable at j+1. -/
theorem binomialMoment_weighted (P : PMF Ω) (h : ℕ → Ω → H) (X : ℕ → Ω → ℕ)
    (m : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (href : Refining h m)
    (hunit : ∀ ω, UnitIncrements (fun i => X i ω) m)
    (had : ∀ i ≤ m, HistoryMeasurable (h i) (X i))
    (htail : ∀ i ≤ m, ∀ a, 0 < probability P (fun ω => h i ω = h i a) →
      conditionalExpect P (fun ω => (X m ω - X i ω : ℕ))
        (fun ω => h i ω = h i a) ≤ γ)
    (r i : ℕ) (hi : i ≤ m) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (haw : HistoryMeasurable (h i) w) :
    expect P (fun ω => w ω * ((X m ω - X i ω).choose r : ℝ)) ≤
      γ ^ r * expect P w := by
  induction r generalizing i w with
  | zero => simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, pow_zero, one_mul, le_refl]
  | succ r ih =>
    have he : expect P (fun ω => w ω * ((X m ω - X i ω).choose (r+1) : ℝ)) =
        ∑ j ∈ Finset.Ico i m, expect P (fun ω =>
          (w ω * (X (j+1) ω - X j ω : ℕ)) * ((X m ω - X (j+1) ω).choose r : ℝ)) := by
      have hh (ω : Ω) := unit_binomial_identity (hunit ω) hi r
      simp_rw [hh, Finset.mul_sum, ← mul_assoc]
      exact expect_sum P _ _
    rw [he]
    calc
      _ ≤ ∑ j ∈ Finset.Ico i m, γ^r * expect P (fun ω =>
          w ω * (X (j+1) ω - X j ω : ℕ)) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hij, hjm⟩ := Finset.mem_Ico.mp hj
        apply ih (j+1) (by omega) _ (fun ω => mul_nonneg (hw ω) (Nat.cast_nonneg _))
        intro ω v hv
        have hwv := haw ω v (href i (j+1) (by omega) (by omega) ω v hv)
        have hx1 := had (j+1) (by omega) ω v hv
        have hx0 := had j (by omega) ω v (href j (j+1) (by omega) (by omega) ω v hv)
        dsimp only
        rw [hwv, hx1, hx0]
      _ = γ^r * expect P (fun ω => w ω * (X m ω - X i ω : ℕ)) := by
        rw [← Finset.mul_sum, ← expect_sum]
        congr 2
        funext ω
        rw [← Finset.mul_sum, ← Nat.cast_sum, unit_increment_sum (hunit ω) hi]
      _ ≤ γ^r * (γ * expect P w) := mul_le_mul_of_nonneg_left
        (expect_mul_le_of_conditional P (h i) _ w γ hw haw (htail i hi)) (pow_nonneg hγ r)
      _ = _ := by rw [pow_succ]; ring

/-- Conditional binomial moments for an adapted process with a uniform terminal-tail bound. -/
theorem binomialMoment (P : PMF Ω) (h : ℕ → Ω → H) (X : ℕ → Ω → ℕ)
    (m : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (href : Refining h m)
    (hunit : ∀ ω, UnitIncrements (fun i => X i ω) m)
    (had : ∀ i ≤ m, HistoryMeasurable (h i) (X i))
    (htail : ∀ i ≤ m, ∀ a, 0 < probability P (fun ω => h i ω = h i a) →
      conditionalExpect P (fun ω => (X m ω - X i ω : ℕ))
        (fun ω => h i ω = h i a) ≤ γ)
    (r i : ℕ) (hi : i ≤ m) (a : Ω) :
    conditionalExpect P (fun ω => ((X m ω - X i ω).choose r : ℝ))
      (fun ω => h i ω = h i a) ≤ γ^r := by
  apply conditional_le_of_weighted P (h i) _ (γ^r) (pow_nonneg hγ r)
  exact fun w hw haw => binomialMoment_weighted P h X m γ hγ href hunit had htail r i hi w hw haw

/-- Source stopped-binomial-moment estimate, with actual quotient conditioning and B_0. -/
theorem stoppedBinomialMoment (P : PMF Ω) (h : ℕ → Ω → H) (X : ℕ → Ω → ℕ)
    (B : ℕ → Ω → Prop) (m : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (href : Refining h m) (hunit : ∀ ω, UnitIncrements (fun i => X i ω) m)
    (had : ∀ i ≤ m, HistoryMeasurable (h i) (X i))
    (hB : ∀ i ≤ m, HistoryMeasurable (h i) (B i))
    (htail : ∀ i < m, ∀ a, B i a → 0 < probability P (fun ω => h i ω = h i a) →
      conditionalExpect P (fun ω => (X m ω - X i ω : ℕ))
        (fun ω => h i ω = h i a) ≤ γ)
    (r i : ℕ) (hi : i ≤ m) (a : Ω) :
    conditionalExpect P
      (fun ω => ((stoppedProcess X B m ω - stoppedProcess X B i ω).choose r : ℝ))
      (fun ω => h i ω = h i a) ≤ γ^r :=
  binomialMoment P h (stoppedProcess X B) m γ hγ href
    (stoppedProcess_unit B hunit) (fun i hi => stoppedProcess_adapted href X B had hB hi)
    (fun i hi a _ => stoppedTail P h X B m γ hγ href hunit hB htail i hi a) r i hi a

end RiffleUpperV2.Exponential
