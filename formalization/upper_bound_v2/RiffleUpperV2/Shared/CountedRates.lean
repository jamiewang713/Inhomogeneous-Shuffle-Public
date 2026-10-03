import RiffleUpperV2.Shared.WindowRates

noncomputable section
namespace RiffleUpperV2

/-- Even after the full prefix count and any fixed real power, the omitted
window error is smaller than any prescribed inverse power. -/
theorem countedWindowError_power_rate (k : ℕ) (hk : 1 ≤ k)
    (T delta epsilon M : ℝ) (hT : 0 ≤ T) (hdelta : 0 < delta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N d : ℕ, N0 ≤ N →
      (d : ℝ) ≤ T * Real.log (N : ℝ) →
      (N : ℝ)^epsilon * (((d : ℝ)+1)*(k : ℝ)^d) *
        Real.exp (-(N : ℝ)^(delta/16)) ≤ (N : ℝ)^(-M) := by
  obtain ⟨N1,hN1,hcount⟩ := countedWindowError_rate k hk T delta hT hdelta
  obtain ⟨N2,hN2,hpower⟩ := powerExp_eventually_le
    (by positivity : 0 < delta/32) (by positivity : (0 : ℝ) < delta/32)
    (by norm_num : (0 : ℝ) < 1) (epsilon+M)
  refine ⟨max N1 N2,hN1.trans (le_max_left _ _),?_⟩
  intro N d hN hd
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := hpower N ((le_max_right _ _).trans hN)
  norm_num only [Real.rpow_zero,neg_one_mul] at hp
  have hp' : (N : ℝ)^(epsilon+M) * Real.exp (-(N : ℝ)^(delta/32)) ≤ 1 :=
    hp.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hfinal : (N : ℝ)^epsilon * Real.exp (-(N : ℝ)^(delta/32)) ≤ (N : ℝ)^(-M) := by
    rw [Real.rpow_neg hNp.le,← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp M)).mpr
    calc
      _ = (N : ℝ)^(epsilon+M) * Real.exp (-(N : ℝ)^(delta/32)) := by
        rw [Real.rpow_add hNp]
        ring
      _ ≤ 1 := hp'
  calc
    _ = (N : ℝ)^epsilon * ((((d : ℝ)+1)*(k : ℝ)^d) *
        Real.exp (-(N : ℝ)^(delta/16))) := by ring
    _ ≤ (N : ℝ)^epsilon * Real.exp (-(N : ℝ)^(delta/32)) :=
      mul_le_mul_of_nonneg_left (hcount N d ((le_max_left _ _).trans hN) hd)
        (Real.rpow_nonneg hNp.le _)
    _ ≤ _ := hfinal

/-- The actual at-edge multiplicity factor costs an arbitrarily small power. -/
theorem relevantMultiplicity_power_rate (k : ℕ) (T epsilon : ℝ)
    (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N d : ℕ, N0 ≤ N →
      (d : ℝ) ≤ T * Real.log (N : ℝ) →
      ((2*k*d+1 : ℕ) : ℝ) ≤ (N : ℝ)^epsilon := by
  obtain ⟨N0,hN0,h⟩ := Compat.fixed_polynomial_le_rpow
    (2*(k : ℝ)+1) T 1 epsilon (by positivity) hT hepsilon
  refine ⟨N0,hN0,?_⟩
  intro N d hN hd
  have hb : ((2*k*d+1 : ℕ) : ℝ) ≤ (2*(k : ℝ)+1)*((d : ℝ)+1) := by
    push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k),
      (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  exact hb.trans (by simpa only [pow_one,Nat.cast_add,Nat.cast_one] using h N d hN hd)

end RiffleUpperV2
