import RiffleUpperV2.Hypergeometric.Main

/-! The finite sum symmetry proof is a namespace-only public adapter copied from
immutable lower Compat/HypergeometricConcentration. Its private export cannot be
called downstream. Provenance and exact source hash are in audit/U03. -/
noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open RiffleLowerV2 RiffleLowerV2.Thinning.Compat RiffleLowerV2.Thinning.Compat.HypergeomParams

def swappedParams (p : HypergeomParams) : HypergeomParams where
  population := p.population
  marked := p.draws
  draws := p.marked
  marked_le := p.draws_le
  draws_le := p.marked_le

private def extendedWeight (p : HypergeomParams) (q : ℕ) : ℝ :=
  if q ≤ p.draws then
    (p.marked.choose q : ℝ) * ((p.population - p.marked).choose (p.draws - q) : ℝ) /
      (p.population.choose p.draws : ℝ)
  else 0

private theorem expect_eq_extended_sum (p : HypergeomParams) (f : ℕ → ℝ) :
    p.law.expect (fun q => f q.val) =
      ∑ q ∈ Finset.range (p.population + 1), extendedWeight p q * f q := by
  unfold FiniteLaw.expect
  simp only [law_mass, weight]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => (p.marked.choose q : ℝ) *
      ((p.population - p.marked).choose (p.draws - q) : ℝ) /
      (p.population.choose p.draws : ℝ) * f q) (p.draws + 1)]
  calc
    _ = ∑ q ∈ Finset.range (p.draws + 1), extendedWeight p q * f q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqd : q ≤ p.draws := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
      simp only [extendedWeight, hqd, ↓reduceIte]
    _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ p.draws_le)) (by
      intro q _ hq
      have hqd : ¬q ≤ p.draws := by
        simp only [Finset.mem_range] at hq
        omega
      simp [extendedWeight, hqd])

private theorem extendedWeight_swappedParams (p : HypergeomParams) (q : ℕ) :
    extendedWeight p q = extendedWeight (swappedParams p) q := by
  by_cases hqm : q ≤ p.draws
  · by_cases hqK : q ≤ p.marked
    · simp only [extendedWeight, swappedParams, hqm, hqK, ↓reduceIte]
      by_cases hrest : p.draws - q ≤ p.population - p.marked
      · have hrest' : p.marked - q ≤ p.population - p.draws := by
          have := p.marked_le
          have := p.draws_le
          omega
        rw [Nat.cast_choose ℝ hqK, Nat.cast_choose ℝ hrest,
          Nat.cast_choose ℝ p.draws_le, Nat.cast_choose ℝ hqm,
          Nat.cast_choose ℝ hrest', Nat.cast_choose ℝ p.marked_le]
        have hres : p.population - p.marked - (p.draws - q) =
            p.population - p.draws - (p.marked - q) := by omega
        rw [hres]
        have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by
          exact_mod_cast Nat.factorial_ne_zero n
        field_simp
      · have hrest' : p.population - p.draws < p.marked - q := by
          have := p.marked_le
          have := p.draws_le
          omega
        simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hrest),
          Nat.choose_eq_zero_of_lt hrest']
    · simp [extendedWeight, swappedParams, hqm, hqK,
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hqK)]
  · by_cases hqK : q ≤ p.marked
    · simp [extendedWeight, swappedParams, hqm, hqK,
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hqm)]
    · simp [extendedWeight, swappedParams, hqm, hqK]

theorem hypergeometricSwappedExpect (p : HypergeomParams) (f : ℕ → ℝ) :
    p.law.expect (fun q => f q.val) =
      (swappedParams p).law.expect (fun q => f q.val) := by
  rw [expect_eq_extended_sum, expect_eq_extended_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [extendedWeight_swappedParams]


/-- PMF-facing symmetry transports arbitrary count observables. -/
theorem hypergeometricSwappedExpectPMF (p : HypergeomParams) (f : ℕ → ℝ) :
    expect p.law.toPMF (fun q => f q.val) =
      expect (swappedParams p).law.toPMF (fun q => f q.val) := by
  rw [Hypergeometric.finiteLaw_expect, Hypergeometric.finiteLaw_expect]
  exact hypergeometricSwappedExpect p f

theorem hypergeometricSwappedProbability (p : HypergeomParams) (E : ℕ → Prop) :
    probability p.law.toPMF (fun q => E q.val) =
      probability (swappedParams p).law.toPMF (fun q => E q.val) := by
  classical
  exact hypergeometricSwappedExpectPMF p (fun q => if E q then 1 else 0)

@[simp] theorem swappedParams_mean (p : HypergeomParams) :
    (swappedParams p).mean = p.mean := by
  simp only [HypergeomParams.mean, swappedParams]
  ring

@[simp] theorem swappedParams_variance (p : HypergeomParams) :
    (swappedParams p).varianceFormula = p.varianceFormula := by
  simp only [HypergeomParams.varianceFormula, swappedParams]
  ring

end RiffleUpperV2.Anchor
