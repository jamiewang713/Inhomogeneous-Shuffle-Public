import RiffleUpperV2.Exponential.Moments

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exponential
open RiffleLowerV2.Thinning

/-- Finite binomial expansion padded by vanishing binomial coefficients. -/
theorem padded_binomial (q : ℝ) {s m : ℕ} (hsm : s ≤ m) :
    (1+q)^s = ∑ r ∈ Finset.range (m+1), q^r * (s.choose r : ℝ) := by
  have he : (1+q)^s = ∑ r ∈ Finset.range (s+1), q^r * (s.choose r : ℝ) := by
    rw [add_comm, add_pow]
    simp
  rw [he]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro r hr hn
  have hsr : s < r := by have := Finset.mem_range.not.mp hn; omega
  simp [Nat.choose_eq_zero_of_lt hsr]

/-- A finite geometric tail lies below the full geometric tail; no limit theorem is needed. -/
theorem finite_geometric_excess {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (m : ℕ) :
    (∑ r ∈ Finset.range (m+1), a^r) - 1 ≤ a / (1-a) := by
  have hpos : 0 < 1-a := sub_pos.mpr ha1
  have hs : (∑ r ∈ Finset.range (m+1), a^r) * (1-a) = 1-a^(m+1) := by
    have hh := geom_sum_mul a (m+1)
    nlinarith
  apply (le_div_iff₀ hpos).mpr
  have hp : 0 ≤ a^(m+1) := pow_nonneg ha _
  nlinarith

variable {Ω H : Type*} [Fintype Ω] [Fintype H]

/-- Exponential excess from uniform conditional terminal tails for an adapted count. -/
theorem excess_of_tail (P : PMF Ω) (h : ℕ → Ω → H) (X : ℕ → Ω → ℕ)
    (m : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (href : Refining h m)
    (hunit : ∀ ω, UnitIncrements (fun i => X i ω) m)
    (hzero : ∀ ω, X 0 ω = 0) (had : ∀ i ≤ m, HistoryMeasurable (h i) (X i))
    (htail : ∀ i ≤ m, ∀ a, 0 < probability P (fun ω => h i ω = h i a) →
      conditionalExpect P (fun ω => (X m ω - X i ω : ℕ))
        (fun ω => h i ω = h i a) ≤ γ)
    (q : ℝ) (hq : 0 ≤ q) (hqγ : q*γ < 1) :
    expect P (fun ω => (1+q)^(X m ω) - 1) ≤ q*γ/(1-q*γ) := by
  have hmom (r : ℕ) : expect P (fun ω => ((X m ω).choose r : ℝ)) ≤ γ^r := by
    have hh := binomialMoment_weighted P h X m γ hγ href hunit had htail r 0
      (Nat.zero_le _) (fun _ => 1) (fun _ => by norm_num) (fun _ _ _ => rfl)
    simpa only [hzero, Nat.sub_zero, one_mul, expect, RiffleLowerV2.Model.expect_const,
      mul_one] using hh
  have hexpand (ω : Ω) := padded_binomial q (unit_terminal_le (hunit ω) (hzero ω))
  calc
    _ = (∑ r ∈ Finset.range (m+1), q^r * expect P
        (fun ω => ((X m ω).choose r : ℝ))) - 1 := by
      simp_rw [hexpand]
      simp only [expect, RiffleLowerV2.expect, mul_sub, Finset.sum_sub_distrib,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      have hsum : ∑ ω, (P ω).toReal * 1 = 1 :=
        RiffleLowerV2.Model.expect_const P 1
      rw [hsum]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ (∑ r ∈ Finset.range (m+1), (q*γ)^r) - 1 := by
      apply sub_le_sub_right
      apply Finset.sum_le_sum
      intro r _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (hmom r) (pow_nonneg hq _)
    _ ≤ _ := finite_geometric_excess (mul_nonneg hq hγ) hqγ m

/-- Source adapted exponential excess. The event C is used only for pathwise domination;
no measurability of C at any intermediate history is assumed. -/
theorem adaptedExcess (P : PMF Ω) (h : ℕ → Ω → H) (X : ℕ → Ω → ℕ)
    (B : ℕ → Ω → Prop) (m : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (href : Refining h m) (hunit : ∀ ω, UnitIncrements (fun i => X i ω) m)
    (hzero : ∀ ω, X 0 ω = 0) (had : ∀ i ≤ m, HistoryMeasurable (h i) (X i))
    (hB : ∀ i ≤ m, HistoryMeasurable (h i) (B i))
    (htail : ∀ i < m, ∀ a, B i a → 0 < probability P (fun ω => h i ω = h i a) →
      conditionalExpect P (fun ω => (X m ω - X i ω : ℕ))
        (fun ω => h i ω = h i a) ≤ γ)
    (C : Ω → Prop) (hC : ∀ ω, C ω → goodPrefix B m ω)
    (t : ℝ) (ht : 0 ≤ t) (htγ : (Real.exp t - 1)*γ < 1) :
    expect P (fun ω => if C ω then Real.exp (t * X m ω) - 1 else 0) ≤
      (Real.exp t - 1)*γ / (1-(Real.exp t - 1)*γ) := by
  have hq : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht)
  have he := excess_of_tail P h (stoppedProcess X B) m γ hγ href
    (stoppedProcess_unit B hunit) (stoppedProcess_zero X B)
    (fun i hi => stoppedProcess_adapted href X B had hB hi)
    (fun i hi a _ => stoppedTail P h X B m γ hγ href hunit hB htail i hi a)
    (Real.exp t - 1) hq htγ
  apply le_trans (expect_mono P (fun ω => ?_)) he
  have hexp : (1 + (Real.exp t - 1))^(stoppedProcess X B m ω) =
      Real.exp (t * stoppedProcess X B m ω) := by
    rw [show 1 + (Real.exp t - 1) = Real.exp t by ring, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  by_cases hc : C ω
  · simp only [hc, if_true, stoppedProcess_eq_on_good hunit hzero ω (hC ω hc), le_refl]
  · simp only [hc, if_false]
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ht (Nat.cast_nonneg _)))

end RiffleUpperV2.Exponential
