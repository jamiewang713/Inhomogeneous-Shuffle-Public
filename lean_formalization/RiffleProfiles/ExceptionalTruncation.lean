import RiffleProfiles.WordMass
import RiffleTimeProfile.Ambient
import Mathlib.Algebra.Order.Floor.Semiring

/-! T06: finite exceptional-prefix truncation with word-dependent endpoints. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace RiffleProfiles

attribute [local instance] Classical.propDecidable

variable {k K : ℕ}

/-- The source's exceptional digits at a fixed column. -/
def sourceExceptionalDigits (p : Fin K → TimeProfile.Simplex k)
    (P : TimeProfile.BorelPartition k) (χ : ℝ) (j : Fin K) : Finset (Fin k) :=
  Finset.univ.filter fun a => ¬ P.IsGoodDigit χ (p j) a

/-- The literal source exceptional filter, with arbitrary word-dependent endpoints. -/
def sourceExceptionalPositions (p : Fin K → TimeProfile.Simplex k)
    (P : TimeProfile.BorelPartition k) (χ : ℝ)
    (v M : (Fin K → Fin k) → ℕ) (ω : Fin K → Fin k) : Finset (Fin K) :=
  (TimeProfile.positions K (v ω) (M ω)).filter
    fun j => ¬ P.IsGoodDigit χ (p j) (ω j)

theorem sourceExceptionalPositions_subset (p : Fin K → TimeProfile.Simplex k)
    (P : TimeProfile.BorelPartition k) (χ : ℝ)
    (v M : (Fin K → Fin k) → ℕ) (ω : Fin K → Fin k) :
    sourceExceptionalPositions p P χ v M ω ⊆
      badPositions (sourceExceptionalDigits p P χ) ω := by
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
    Finset.mem_filter.mpr ⟨Finset.mem_univ (ω j), (Finset.mem_filter.mp hj).2⟩⟩

theorem sourceExceptionalDigits_prob_le (p : Fin K → TimeProfile.Simplex k)
    (P : TimeProfile.BorelPartition k) {χ C : ℝ} (hreg : P.IsRegular χ C)
    (j : Fin K) (a : Fin k) (ha : a ∈ sourceExceptionalDigits p P χ j) :
    TimeProfile.prob (p j) a ≤ 3 * χ := by
  exact hreg.exceptional_actual_le (Finset.mem_filter.mp ha).2

/-- The strict normalized exceptional-count event implies the exact natural threshold. -/
theorem exceptionalPrefix_badCount_ge (N : ℕ) (p : Fin K → TimeProfile.Simplex k)
    (P : TimeProfile.BorelPartition k) (χ α : ℝ)
    (v M : (Fin K → Fin k) → ℕ) (hN : 2 ≤ N) (hα : 0 ≤ α)
    (ω : Fin K → Fin k)
    (hevent : α < ((sourceExceptionalPositions p P χ v M ω).card : ℝ) /
      TimeProfile.logScale N) :
    Nat.floor (α * TimeProfile.logScale N) + 1 ≤
      badCount (sourceExceptionalDigits p P χ) ω := by
  have hL := TimeProfile.logScale_pos hN
  have hreal : α * TimeProfile.logScale N <
      ((sourceExceptionalPositions p P χ v M ω).card : ℝ) :=
    (lt_div_iff₀ hL).mp hevent
  have hnat : Nat.floor (α * TimeProfile.logScale N) <
      (sourceExceptionalPositions p P χ v M ω).card :=
    (Nat.floor_lt (mul_nonneg hα hL.le)).mpr hreal
  exact (Nat.succ_le_of_lt hnat).trans
    (Finset.card_le_card (sourceExceptionalPositions_subset p P χ v M ω))

/-- Frozen T06, as an exact finite sum of product-word weights. -/
theorem exceptionalPrefix_wordMass_le (N : ℕ) (p : Fin K → TimeProfile.Simplex k)
    (P : TimeProfile.BorelPartition k) (χ C α : ℝ)
    (v M : (Fin K → Fin k) → ℕ) (hreg : P.IsRegular χ C)
    (hχ : 0 < χ) (hN : 2 ≤ N) (hα : 0 ≤ α) :
    (∑ ω : Fin K → Fin k,
      if α < ((sourceExceptionalPositions p P χ v M ω).card : ℝ) /
          TimeProfile.logScale N
      then wordWeight (fun j a => TimeProfile.prob (p j) a) ω else 0) ≤
      tailWeight K (Nat.floor (α * TimeProfile.logScale N) + 1)
        ((k : ℝ) * (3 * χ)) := by
  have htail := badWordMass_smallDigits_le_tailWeight
    (fun j a => TimeProfile.prob (p j) a) (sourceExceptionalDigits p P χ)
    (fun j a => TimeProfile.prob_nonneg (p j) a)
    (fun j => TimeProfile.sum_prob (p j))
    (mul_pos (by norm_num : (0 : ℝ) < 3) hχ)
    (fun j a ha => sourceExceptionalDigits_prob_le p P hreg j a ha)
    (Nat.floor (α * TimeProfile.logScale N) + 1)
  have hdom : (∑ ω : Fin K → Fin k,
      if α < ((sourceExceptionalPositions p P χ v M ω).card : ℝ) /
          TimeProfile.logScale N
      then wordWeight (fun j a => TimeProfile.prob (p j) a) ω else 0) ≤
      badWordMass (fun j a => TimeProfile.prob (p j) a)
        (sourceExceptionalDigits p P χ) (Nat.floor (α * TimeProfile.logScale N) + 1) := by
    rw [badWordMass, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro ω _hω
    by_cases hevent : α < ((sourceExceptionalPositions p P χ v M ω).card : ℝ) /
        TimeProfile.logScale N
    · have hbad := exceptionalPrefix_badCount_ge N p P χ α v M hN hα ω hevent
      simp only [hevent, hbad, if_pos, le_refl]
    · simp only [hevent, if_false]
      split_ifs
      · exact wordWeight_nonneg _ (fun j a => TimeProfile.prob_nonneg (p j) a) ω
      · exact le_rfl
  exact hdom.trans (by simpa only [Fintype.card_fin] using htail)

/-- Multiplying frozen T06 by the natural number of rows. -/
theorem exceptionalPrefix_scaled_wordMass_le (N : ℕ)
    (p : Fin K → TimeProfile.Simplex k) (P : TimeProfile.BorelPartition k)
    (χ C α : ℝ) (v M : (Fin K → Fin k) → ℕ) (hreg : P.IsRegular χ C)
    (hχ : 0 < χ) (hN : 2 ≤ N) (hα : 0 ≤ α) :
    (N : ℝ) * (∑ ω : Fin K → Fin k,
      if α < ((sourceExceptionalPositions p P χ v M ω).card : ℝ) /
          TimeProfile.logScale N
      then wordWeight (fun j a => TimeProfile.prob (p j) a) ω else 0) ≤
      (N : ℝ) * tailWeight K (Nat.floor (α * TimeProfile.logScale N) + 1)
        ((k : ℝ) * (3 * χ)) := by
  exact mul_le_mul_of_nonneg_left
    (exceptionalPrefix_wordMass_le N p P χ C α v M hreg hχ hN hα) (Nat.cast_nonneg N)

end RiffleProfiles
