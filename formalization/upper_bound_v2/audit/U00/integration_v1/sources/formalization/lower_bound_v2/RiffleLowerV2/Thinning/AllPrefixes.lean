import Contracts.v1.ModelThinning
import RiffleLowerV2.Shared.Adapters

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Thinning
open TimeProfile

/-- Actual variable-length words are counted once, without unused suffix multiplicity. -/
theorem prefix_card_exact (k K : ℕ) :
    Fintype.card (Prefix k K) = ∑ n : Fin (K+1), k^n.val := by
  simp [Prefix, RiffleShuffle.RawPrefix, RiffleShuffle.Word,
    Fintype.card_sigma, card_vector]

/-- The polynomial prefix count bound also includes the one-letter alphabet. -/
theorem prefix_card_le {k K : ℕ} (hk : 1 ≤ k) :
    Fintype.card (Prefix k K) ≤ (K+1) * k^K := by
  rw [prefix_card_exact]
  calc
    ∑ n : Fin (K+1), k^n.val ≤ ∑ _n : Fin (K+1), k^K := by
      apply Finset.sum_le_sum
      intro n _
      exact pow_le_pow_right₀ hk (Nat.le_of_lt_succ n.isLt)
    _ = _ := by simp

/-- Positive decks with a nonempty sequence of columns force a nonempty alphabet. -/
theorem prefix_card_le_of_cuts {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) :
    Fintype.card (Prefix k K) ≤ (K+1) * k^K := by
  by_cases hK : K = 0
  · subst K
    simp
  · apply prefix_card_le
    by_contra hk
    have hk0 : k = 0 := by omega
    subst k
    have hs := cuts.sum_count ⟨0, Nat.pos_of_ne_zero hK⟩
    simp at hs
    omega

/-- The deterministic prefix mean remains nonnegative for every prefix, even of zero mass. -/
theorem prefixMean_nonneg {k N K : ℕ} (cuts : Cuts k N K) (w : Prefix k K) :
    0 ≤ prefixMean cuts w := by
  unfold prefixMean RiffleLowerV2.prefixMass
  positivity

/-- The manuscript's exact substitution into the finite Bernstein denominator. -/
theorem prefix_bernstein_exponent {μ A : ℝ} (hμ : 0 ≤ μ) (hA : 1 ≤ A) :
    A/8 ≤ (A * (Real.sqrt μ + 1))^2 / (4 * (μ + A * (Real.sqrt μ + 1))) := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hs : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg _
  have ht : 0 < A * (Real.sqrt μ + 1) := mul_pos hA0 (by positivity)
  have hden : 0 < 4 * (μ + A * (Real.sqrt μ + 1)) := by positivity
  have hbound : μ + A * (Real.sqrt μ + 1) ≤ 2 * A * (Real.sqrt μ + 1)^2 := by
    calc
      μ + A * (Real.sqrt μ + 1) ≤ A*μ + A*(Real.sqrt μ+1) :=
        by simpa only [add_comm] using
          (add_le_add_right (le_mul_of_one_le_left hμ hA) (A * (Real.sqrt μ + 1)))
      _ = A * (μ + Real.sqrt μ + 1) := by ring
      _ ≤ A * (2 * (Real.sqrt μ+1)^2) := by
        apply mul_le_mul_of_nonneg_left _ hA0.le
        nlinarith [Real.sq_sqrt hμ]
      _ = _ := by ring
  apply (le_div_iff₀ hden).mpr
  calc
    A/8 * (4 * (μ + A * (Real.sqrt μ + 1))) =
        (A/2) * (μ + A * (Real.sqrt μ + 1)) := by ring
    _ ≤ (A/2) * (2 * A * (Real.sqrt μ + 1)^2) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

private theorem prefix_probability_mono {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    {B C : Ω → Prop} (h : ∀ ω, B ω → C ω) : probability P B ≤ probability P C := by
  unfold probability expect
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  by_cases hb : B ω <;> by_cases hc : C ω <;> simp_all

private theorem prefix_probability_union {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : PMF Ω) (B : I → Ω → Prop) :
    probability P (fun ω => ∃ i, B i ω) ≤ ∑ i, probability P (B i) := by
  simp only [probability, expect]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  by_cases hb : ∃ i, B i ω
  · obtain ⟨i, hi⟩ := hb
    simp only [show (∃ i, B i ω) from ⟨i, hi⟩, if_true]
    exact le_trans (by simp [hi])
      (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i))
  · simp only [hb, if_false]
    exact Finset.sum_nonneg fun _ _ => by positivity

/-- A single deterministic prefix has the common exponential failure bound. -/
theorem prefix_failure_of_prefixTails (htails : Targets.PrefixTails)
    {k N K : ℕ} (cuts : Cuts k N K) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε)
    (w : Prefix k K) :
    probability (fixedCountPMF cuts) (fun ω =>
      (N : ℝ)^ε * (Real.sqrt (prefixMean cuts w)+1) ≤
        |(prefixCount w ω : ℝ) - prefixMean cuts w|) ≤
      2 * Real.exp (-(N : ℝ)^ε / 8) := by
  have hA : 1 ≤ (N : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) hε.le
  have ht : 0 < (N : ℝ)^ε * (Real.sqrt (prefixMean cuts w)+1) := by positivity
  have hh := (htails cuts (by omega) w).1 _ ht
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hb := neg_le_neg (prefix_bernstein_exponent (prefixMean_nonneg cuts w) hA)
  simpa only [neg_div] using hb

/-- Every length, zero-mass prefix, and the empty prefix enter the explicit union bound.
The stochastic premise is separately discharged by the concrete prefix-law proof. -/
theorem allPrefixConcentration_of_prefixTails (htails : Targets.PrefixTails) :
    Targets.AllPrefixConcentration := by
  intro k N K cuts hN ε hε
  let B := fun (w : Prefix k K) (ω : Sample cuts) =>
    (N : ℝ)^ε * (Real.sqrt (prefixMean cuts w)+1) ≤
      |(prefixCount w ω : ℝ) - prefixMean cuts w|
  have hm : probability (fixedCountPMF cuts) (fun ω => ¬allPrefixEvent ε ω) ≤
      probability (fixedCountPMF cuts) (fun ω => ∃ w, B w ω) := by
    apply prefix_probability_mono
    intro ω hω
    obtain ⟨w, hw⟩ := not_forall.mp hω
    exact ⟨w, (lt_of_not_ge hw).le⟩
  have hu := prefix_probability_union (fixedCountPMF cuts) B
  have hsingle : ∑ w : Prefix k K, probability (fixedCountPMF cuts) (B w) ≤
      (Fintype.card (Prefix k K) : ℝ) * (2 * Real.exp (-(N : ℝ)^ε / 8)) := by
    calc
      _ ≤ ∑ _w : Prefix k K, 2 * Real.exp (-(N : ℝ)^ε / 8) :=
        Finset.sum_le_sum fun w _ => prefix_failure_of_prefixTails htails cuts hN ε hε w
      _ = _ := by simp
  have hc : (Fintype.card (Prefix k K) : ℝ) ≤ ((K+1) * k^K : ℕ) := by
    exact_mod_cast prefix_card_le_of_cuts cuts (show 0 < N by omega)
  calc
    _ ≤ _ := hm.trans (hu.trans hsingle)
    _ ≤ (((K+1) * k^K : ℕ) : ℝ) * (2 * Real.exp (-(N : ℝ)^ε / 8)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = prefixFailure N k K ε := by
      simp only [prefixFailure, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
      ring

end RiffleLowerV2.Thinning
