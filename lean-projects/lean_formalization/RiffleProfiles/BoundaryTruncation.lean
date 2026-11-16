import Riffle.Boundary
import RiffleProfiles.ModelWordMass

/-! Frozen T03–T04: actual boundary exclusion implies a small-digit tail. -/

noncomputable section
open scoped BigOperators

namespace RiffleProfiles

def boundaryThreshold {D : Riffle.Model} (A : Riffle.Setup D) : ℝ :=
  A.C / Real.log (1 / A.chi) * Real.log (D.N : ℝ)

def boundaryBadDigits {D : Riffle.Model} (A : Riffle.Setup D)
    (s : Riffle.Side) (j : Fin D.K) : Finset (Fin D.k) := by
  classical
  exact Finset.univ.filter fun a => match s with
    | .left => a.val < Riffle.leftIndex A j.val
    | .right => Riffle.rightIndex A j.val < a.val

def discardedBoundary {D : Riffle.Model} (A : Riffle.Setup D)
    (s : Riffle.Side) : Set Riffle.Word :=
  {x | x ∈ Riffle.Cylinder D A.w ∧ Riffle.selected A s x ∉ Riffle.Admissible A s}

theorem boundaryThreshold_pos {D : Riffle.Model} (A : Riffle.Setup D) :
    0 < boundaryThreshold A := by
  have hk : (1 : ℝ) ≤ D.k := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) D.two_le_k)
  have hχ : A.chi < 1 := A.chi_lt.trans_le ((div_le_one (by linarith)).2 hk)
  have hinv : (1 : ℝ) < 1 / A.chi := (lt_div_iff₀ A.chi_pos).2 (by simpa using hχ)
  have hN : (1 : ℝ) < D.N := by exact_mod_cast D.one_lt_N
  exact mul_pos (div_pos A.C_pos (Real.log_pos hinv)) (Real.log_pos hN)

theorem boundaryBadDigits_small {D : Riffle.Model} (A : Riffle.Setup D)
    (s : Riffle.Side) (j : Fin D.K) (a : Fin D.k)
    (ha : a ∈ boundaryBadDigits A s j) : modelDigitProb D j a < A.chi := by
  classical
  cases s with
  | left =>
    apply Riffle.prob_lt_chi_of_lt_left A j.isLt a.isLt
    simpa only [boundaryBadDigits, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  | right =>
    apply Riffle.prob_lt_chi_of_right_lt A j.isLt a.isLt
    simpa only [boundaryBadDigits, Finset.mem_filter, Finset.mem_univ, true_and] using ha

theorem boundary_violations_le_badCount {D : Riffle.Model} (A : Riffle.Setup D)
    (s : Riffle.Side) (x : Riffle.Word) (ω : Riffle.FullIndex D)
    (hx : x <+: Riffle.fullList ω) :
    Riffle.violations A s x ≤ badCount (boundaryBadDigits A s) ω := by
  classical
  have hlen : x.length ≤ D.K := by simpa only [Riffle.fullList_length] using hx.length_le
  let V := (Finset.Ico A.w.length x.length).filter fun i => match s with
    | .left => Riffle.digit x i < Riffle.leftIndex A i
    | .right => Riffle.rightIndex A i < Riffle.digit x i
  have hsub : V ⊆ (badPositions (boundaryBadDigits A s) ω).image Fin.val := by
    intro i hi
    have hiV := Finset.mem_filter.mp hi
    have hiL := (Finset.mem_Ico.mp hiV.1).2
    have hiK := hiL.trans_le hlen
    have hd : Riffle.digit x i = (ω ⟨i, hiK⟩).val :=
      (Riffle.digit_prefix hx hiL).trans (Riffle.fullList_digit ω hiK)
    refine Finset.mem_image.mpr ⟨⟨i, hiK⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases s <;> simpa only [hd] using hiV.2
  calc
    Riffle.violations A s x = V.card := rfl
    _ ≤ ((badPositions (boundaryBadDigits A s) ω).image Fin.val).card :=
      Finset.card_le_card hsub
    _ = badCount (boundaryBadDigits A s) ω := by
      rw [Finset.card_image_of_injective _ Fin.val_injective]
      rfl

theorem discardedBoundary_many_badDigits {D : Riffle.Model} (A : Riffle.Setup D)
    (s : Riffle.Side) (ω : Riffle.FullIndex D)
    (hω : Riffle.fullList ω ∈ discardedBoundary A s) :
    Nat.floor (boundaryThreshold A) + 1 ≤ badCount (boundaryBadDigits A s) ω := by
  have hs := Riffle.selected_spec s hω.1
  have hgt : boundaryThreshold A <
      (Riffle.violations A s (Riffle.selected A s (Riffle.fullList ω)) : ℝ) := by
    apply lt_of_not_ge
    intro hle
    exact hω.2 ⟨hs.1, hle⟩
  have hfloor := (Nat.floor_lt (boundaryThreshold_pos A).le).2 hgt
  exact (Nat.add_one_le_iff.mpr hfloor).trans
    (boundary_violations_le_badCount A s _ ω hs.2)

theorem discardedBoundary_expectedCount_le {D : Riffle.Model} (A : Riffle.Setup D)
    (s : Riffle.Side) :
    (Riffle.expectedCount D (discardedBoundary A s) : ℝ) ≤
      (D.N : ℝ) * tailWeight D.K (Nat.floor (boundaryThreshold A) + 1)
        ((D.k : ℝ) * A.chi) := by
  apply model_expectedCount_le_tailWeight D (boundaryBadDigits A s) _
    (mul_nonneg (Nat.cast_nonneg _) A.chi_pos.le) _ _
    (discardedBoundary_many_badDigits A s)
  intro j
  simpa only [Fintype.card_fin] using
    badDigitMass_le (modelDigitProb D) (boundaryBadDigits A s) A.chi_pos
      (fun i a ha => (boundaryBadDigits_small A s i a ha).le) j

theorem discardedBoundary_union_expectedCount_le {D : Riffle.Model} (A : Riffle.Setup D) :
    (Riffle.expectedCount D (discardedBoundary A .left ∪ discardedBoundary A .right) : ℝ) ≤
      2 * ((D.N : ℝ) * tailWeight D.K (Nat.floor (boundaryThreshold A) + 1)
        ((D.k : ℝ) * A.chi)) := by
  calc
    _ ≤ (Riffle.expectedCount D (discardedBoundary A .left) : ℝ) +
        (Riffle.expectedCount D (discardedBoundary A .right) : ℝ) :=
      model_expectedCount_union_le D _ _
    _ ≤ _ := by
      have hl := discardedBoundary_expectedCount_le A Riffle.Side.left
      have hr := discardedBoundary_expectedCount_le A Riffle.Side.right
      linarith

end RiffleProfiles
