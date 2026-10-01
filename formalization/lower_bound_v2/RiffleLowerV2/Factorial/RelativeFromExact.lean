import RiffleLowerV2.Factorial.Relative
import RiffleLowerV2.Factorial.MomentScales

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiffleLowerV2.Factorial
open TimeProfile

theorem relativeJointFactorial_of_exact (hExact : Targets.ExactJointFactorial) :
    Targets.RelativeJointFactorial := by
  intro c C hc hC
  let a := min c 1
  have ha : 0 < a := lt_min hc (by norm_num)
  obtain ⟨N0, hN02, hN0⟩ := eventual_factorial_budgets ha C
  refine ⟨4/a, by positivity, N0, ?_⟩
  intro N hN k K d hK cuts w r hw hpiles hR
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hb := hN0 N hN
  have ha1 : a ≤ 1 := min_le_right _ _
  have hac : a ≤ c := min_le_left _ _
  have hpop : a*N ≤ (N : ℝ) := by nlinarith
  have hcut : 2*((∑ i, r i) : ℝ) ≤ a*N := by linarith
  have hRN : (∑ i, r i) ≤ N := by
    have : ((∑ i, r i) : ℝ) ≤ N := by nlinarith [Nat.cast_nonneg (α := ℝ) (∑ i, r i)]
    exact_mod_cast this
  have hs (j : Fin K) (x : Fin k) (hx : 0 < requestedCount w r j x) :
      a*N ≤ (cuts.count j x : ℝ) := by
    obtain ⟨i, hi⟩ := requestedCount_pos_selected w r j x hx
    have hh := hpiles i j
    rw [hi] at hh
    exact (mul_le_mul_of_nonneg_right hac hNr.le).trans hh
  have hC0 : 0 ≤ C*logScale N+1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have he : (2/a)*(K+1)*((∑ i, r i) : ℝ)^2/N ≤ 1 := by
    apply le_trans ?_ hb.2
    gcongr
  have hf := relativeFactorial_finite cuts.count (requestedCount w r) ha hNp hpop
    (requestedCount_sum w r) hs (by simpa only [Nat.cast_sum] using hcut)
      (by simpa only [Nat.cast_sum] using he)
  rw [hExact cuts w r hw hRN, factorial_benchmark_identity]
  simpa only [exactFactorial, numericalMean, Nat.cast_sum] using hf

theorem residualRelativeFactorial_of_exact (hExact : Targets.ResidualJointFactorial) :
    Targets.ResidualRelativeFactorial := by
  intro c C hc hC b0
  let a := min (c/2) (1/2)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  obtain ⟨N1, hN12, hN1⟩ := eventual_factorial_budgets ha C
  let N0 := max N1 (max (2*b0+2) ⌈2*(b0 : ℝ)/c⌉₊)
  have hb0N0 : b0 < N0 := by dsimp [N0]; omega
  have hN02 : 2 ≤ N0 := by dsimp [N0]; omega
  refine ⟨4/a, by positivity, N0, hb0N0, hN02, ?_⟩
  intro N hN k K b d hbb hK cuts p hpinj hp w r hw hpiles hR
  have hNN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hNN2 : 2*b0+2 ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hNceil : ⌈2*(b0 : ℝ)/c⌉₊ ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hbN : b < N := by omega
  have hbR : (b : ℝ) ≤ b0 := by exact_mod_cast hbb
  have hbc0 : 2*(b0 : ℝ) ≤ c*N := by
    have hh : 2*(b0 : ℝ)/c ≤ (N : ℝ) :=
      (Nat.le_ceil (2*(b0 : ℝ)/c)).trans (by exact_mod_cast hNceil)
    have := (div_le_iff₀ hc).mp hh
    nlinarith
  have ha1 : a ≤ 1/2 := min_le_right _ _
  have hac : a ≤ c/2 := min_le_left _ _
  have hpop : a*N ≤ ((N-b : ℕ) : ℝ) := by
    rw [Nat.cast_sub hbN.le]
    have hh : (2 : ℝ)*b0+2 ≤ N := by exact_mod_cast hNN2
    nlinarith
  have hb := hN1 N hNN1
  have hcut : 2*((∑ i, r i) : ℝ) ≤ a*N := by linarith
  have hRN : (∑ i, r i) ≤ N-b := by
    have : ((∑ i, r i) : ℝ) ≤ (N-b : ℕ) := by nlinarith [Nat.cast_nonneg (α := ℝ) (∑ i, r i)]
    exact_mod_cast this
  let n : Fin K → Fin k → ℕ := fun j x => cuts.count j x - usedCount p j x
  have hs (j : Fin K) (x : Fin k) (hx : 0 < requestedCount w r j x) :
      a*N ≤ (n j x : ℝ) := by
    obtain ⟨i, hi⟩ := requestedCount_pos_selected w r j x hx
    have hh := hpiles i j
    rw [hi] at hh
    have hu : (usedCount p j x : ℝ) ≤ b := by exact_mod_cast usedCount_le p j x
    have hun : usedCount p j x ≤ cuts.count j x := by
      have : (usedCount p j x : ℝ) ≤ cuts.count j x := by nlinarith
      exact_mod_cast this
    dsimp [n]
    rw [Nat.cast_sub hun]
    nlinarith
  have hC0 : 0 ≤ C*logScale N+1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have he : (2/a)*(K+1)*((∑ i, r i) : ℝ)^2/N ≤ 1 := by
    apply le_trans ?_ hb.2
    gcongr
  have hf := relativeFactorial_finite n (requestedCount w r) ha hNp hpop
    (requestedCount_sum w r) hs (by simpa only [Nat.cast_sum] using hcut)
      (by simpa only [Nat.cast_sum] using he)
  have hbench : ∏ i, (Targets.residualWordMean cuts p (w i))^(r i) =
      numericalMean (((N-b : ℕ) : ℝ)^(∑ i, r i))
        (fun j => ∏ x, (n j x : ℝ)^requestedCount w r j x) := by
    exact numericalMean_product_benchmark (N-b : ℕ) (fun j x => (n j x : ℝ)) w r
  rw [hExact cuts p hbN hpinj hp w r hw hRN, hbench]
  simpa only [numericalMean, n, Nat.cast_sum] using hf

end RiffleLowerV2.Factorial
