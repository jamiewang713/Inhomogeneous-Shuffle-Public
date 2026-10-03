import RiffleUpperV2.Anchor.UnequalParameters
import RiffleUpperV2.Anchor.EqualMeans

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric

def SuffixSide.containingDigits {k : ℕ} (s : SuffixSide) (a : Fin k) :=
  Finset.univ.filter (fun b => match s with | .lower => b ≤ a | .upper => a ≤ b)

def SuffixSide.oppositeDigits {k : ℕ} (s : SuffixSide) (a : Fin k) :=
  Finset.univ.filter (fun b => match s with | .lower => a < b | .upper => b < a)

def oppositeMean {k n d : ℕ} (s : SuffixSide) (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) : ℝ :=
  match s with | .lower => rightMean cuts R x j | .upper => leftMean cuts R x j

theorem unequal_digitSets {k : ℕ} (a : Fin k) :
    SuffixSide.lower.allowed a = SuffixSide.lower.containingDigits a ∧
    Finset.univ \ SuffixSide.lower.allowed a = SuffixSide.lower.oppositeDigits a ∧
    SuffixSide.upper.allowed a = SuffixSide.upper.oppositeDigits a ∧
    Finset.univ \ SuffixSide.upper.allowed a = SuffixSide.upper.containingDigits a := by
  refine ⟨rfl,?_,rfl,?_⟩ <;> ext b <;>
    simp [SuffixSide.allowed, SuffixSide.containingDigits, SuffixSide.oppositeDigits]

theorem containing_digitProbability {k n d : ℕ} (cuts : Cuts k n d)
    (s : SuffixSide) (j : Fin d) (a : Fin k) :
    digitProbability cuts j a ≤ (allowedCount cuts j (s.containingDigits a) : ℝ)/n := by
  have hc : cuts.count j a ≤ allowedCount cuts j (s.containingDigits a) := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    change a ∈ Finset.univ.filter _
    cases s <;> simp
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg n)

theorem oppositeMean_eq {k n d : ℕ} (cuts : Cuts k n d)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) :
    oppositeMean s cuts R x j = (R.card : ℝ)*sidePrefixMass cuts x j *
      ((allowedCount cuts (prefixColumn x j) (s.oppositeDigits (x.2.get j)) : ℝ)/n) := by
  cases s <;> simp only [oppositeMean, leftMean, rightMean, leftProbability, rightProbability, SuffixSide.oppositeDigits]

theorem witnessMean_le_card {k n d : ℕ} (cuts : Cuts k n d)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val) :
    witnessMean cuts s R x i j ≤ R.card := by
  have hh := mul_le_mul_of_nonneg_left (cylinderMass_bounds cuts (witnessDigits s x i j)).2
    (Nat.cast_nonneg R.card)
  change (R.card : ℝ) * cylinderMass cuts (witnessDigits s x i j) ≤ R.card
  simpa only [mul_one] using hh

theorem unequal_side_count_bounds {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    (hji : j.val < i.val) :
    sideMean s cuts R x i ≤ allowedCount cuts (prefixColumn x j) (s.containingDigits (x.2.get j)) ∧
    oppositeMean s cuts R x j ≤ allowedCount cuts (prefixColumn x j) (s.oppositeDigits (x.2.get j)) := by
  have hM : (R.card : ℝ) ≤ n := by exact_mod_cast (by simpa using Finset.card_le_univ R : R.card ≤ n)
  have hw₀ : 0 ≤ witnessMean cuts s R x i j := mul_nonneg (Nat.cast_nonneg _) (cylinderMass_bounds cuts _).1
  have hd₀ : 0 ≤ digitProbability cuts (prefixColumn x j) (x.2.get j) := by unfold digitProbability; positivity
  have hc₀ : 0 ≤ (allowedCount cuts (prefixColumn x j) (s.containingDigits (x.2.get j)) : ℝ)/n := by positivity
  have ho₀ : 0 ≤ (allowedCount cuts (prefixColumn x j) (s.oppositeDigits (x.2.get j)) : ℝ)/n := by positivity
  constructor
  · rw [← witnessMean_mul_digit cuts hn s R x i j hji]
    calc
      _ ≤ (R.card : ℝ)*((allowedCount cuts (prefixColumn x j) (s.containingDigits (x.2.get j)) : ℝ)/n) :=
        mul_le_mul (witnessMean_le_card cuts s R x i j) (containing_digitProbability cuts s _ _) hd₀ (Nat.cast_nonneg _)
      _ ≤ (n : ℝ)*((allowedCount cuts (prefixColumn x j) (s.containingDigits (x.2.get j)) : ℝ)/n) :=
        mul_le_mul_of_nonneg_right hM hc₀
      _ = _ := by field_simp
  · rw [oppositeMean_eq]
    calc
      _ ≤ (R.card : ℝ)*((allowedCount cuts (prefixColumn x j) (s.oppositeDigits (x.2.get j)) : ℝ)/n) := by
        nlinarith [mul_le_mul_of_nonneg_right (sidePrefixMass_le_one cuts hn x j)
          (mul_nonneg (Nat.cast_nonneg R.card) ho₀)]
      _ ≤ (n : ℝ)*((allowedCount cuts (prefixColumn x j) (s.oppositeDigits (x.2.get j)) : ℝ)/n) :=
        mul_le_mul_of_nonneg_right hM ho₀
      _ = _ := by field_simp

theorem oppositeMean_div_card {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (hM : 0 < R.card) (x : Prefix k d) (j : Fin x.1.val) :
    oppositeMean s cuts R x j / R.card ≤
      (allowedCount cuts (prefixColumn x j) (s.oppositeDigits (x.2.get j)) : ℝ)/n := by
  apply (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < R.card)).mpr
  rw [oppositeMean_eq]
  have ho₀ : 0 ≤ (allowedCount cuts (prefixColumn x j) (s.oppositeDigits (x.2.get j)) : ℝ)/n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (sidePrefixMass_le_one cuts hn x j)
    (mul_nonneg (Nat.cast_nonneg R.card) ho₀)]

end RiffleUpperV2.Anchor
