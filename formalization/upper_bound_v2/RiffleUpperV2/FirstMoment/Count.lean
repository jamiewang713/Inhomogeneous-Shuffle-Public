import RiffleUpperV2.FirstMoment.ClassAdapters
import RiffleUpperV2.Compat.EmpiricalCountLimits
import RiffleUpperV2.Compat.FixedPolynomial

noncomputable section
namespace RiffleUpperV2.FirstMoment
local instance {A : Sort*} : DecidableEq A := Classical.typeDecidableEq A
open TimeProfile InhomogeneousShuffle.FirstMoment

def boundaryBudget (N : ℕ) (C chi : ℝ) : ℕ :=
  ⌊(C / Real.log (1/chi))*logScale N⌋₊

def extensionBudget (N : ℕ) (chi : ℝ) : ℕ :=
  ⌊exceptionalAllowance chi*logScale N⌋₊

def empiricalBinCount (T chi width : ℝ) : ℕ :=
  1+⌊T*Real.log (1/chi)/width⌋₊

/-- The old finite counting polynomial is used solely as finite combinatorics. -/
theorem card_empiricalKey_eq_profileCount (k d qb qe bins : ℕ) :
    Fintype.card (EmpiricalKey k d qb qe bins) =
      k*bins*profileCountBound d k qb qe 0 := by
  rw [card_empiricalKey]
  simp only [profileCountBound, zero_add]
  ring

/-- Uniform original-scale retained descriptor count. C is fixed before chi;
width is any fixed positive number and the threshold is independent of arrays. -/
theorem empiricalCostClassCount (k : ℕ) (T C epsilon : ℝ)
    (hk : 2 ≤ k) (hT : 0 ≤ T) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < min 1 (1/(k : ℝ)) ∧
      ∀ chi : ℝ, 0 < chi → chi < chi0 → ∀ width : ℝ, 0 < width →
        ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N d : ℕ, N0 ≤ N →
          (d : ℝ) ≤ T*logScale N →
          (Fintype.card (EmpiricalKey k d (boundaryBudget N C chi)
            (extensionBudget N chi) (empiricalBinCount T chi width)) : ℝ) ≤
            (N : ℝ)^epsilon := by
  obtain ⟨chi0,hchi0,hchi0k,hsmall⟩ := Compat.profileCount_small_chi k T C (epsilon/2)
    hk hT hC (by positivity)
  refine ⟨chi0,hchi0,hchi0k,?_⟩
  intro chi hchi hchilt width hwidth
  obtain ⟨N1,hN1,hcount⟩ := hsmall chi hchi hchilt 0
  obtain ⟨N2,hN2,hfactor⟩ := Compat.fixed_polynomial_le_rpow
    ((k : ℝ)*empiricalBinCount T chi width) T 0 (epsilon/2) (by positivity) hT (by positivity)
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N d hN hd
  have hNN1 := (le_max_left N1 N2).trans hN
  have hNN2 := (le_max_right N1 N2).trans hN
  have hp := hcount N d hNN1 hd
  have hf := hfactor N d hNN2 hd
  simp only [pow_zero,mul_one] at hf
  rw [card_empiricalKey_eq_profileCount, Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ (N : ℝ)^(epsilon/2)*(N : ℝ)^(epsilon/2) :=
      mul_le_mul hf hp (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (N : ℝ)^epsilon := by
      rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < N))]
      congr 1
      ring

/-- Every realized image inherits the uniform descriptor count, including images
restricted by stability, legality, boundary consistency and terminal routing. -/
theorem realizedClassCount_le {A : Type*} [Fintype A] {k d qb qe bins N : ℕ}
    (descriptor : A → EmpiricalKey k d qb qe bins) {epsilon : ℝ}
    (hcount : (Fintype.card (EmpiricalKey k d qb qe bins) : ℝ) ≤ (N : ℝ)^epsilon) :
    ((Finset.univ.image descriptor).card : ℝ) ≤ (N : ℝ)^epsilon := by
  classical
  exact (Nat.cast_le.mpr (Finset.card_le_univ _)).trans hcount

end RiffleUpperV2.FirstMoment
