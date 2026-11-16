import RiffleUpperV2.Anchor.CylinderExtension
import RiffleUpperV2.Anchor.SliceOrder

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric RiffleUpperV2.Localization

def SuffixSide.strictDigits {k : ℕ} (s : SuffixSide) (a : Fin k) :=
  Finset.univ.filter (fun b => s.test b a)

def sideMean {k n d : ℕ} (s : SuffixSide) (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) : ℝ :=
  match s with | .lower => leftMean cuts R x i | .upper => rightMean cuts R x i

def witnessDigits {k d : ℕ} (s : SuffixSide) (x : Prefix k d)
    (i j : Fin x.1.val) :=
  Function.update (prefixThenDigits x i (s.strictDigits (x.2.get i))) (prefixColumn x j) Finset.univ

def witnessRows {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val) (ω : Sample cuts) :=
  cylinderSet cuts R (witnessDigits s x i j) ω

def witnessMean {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val) : ℝ :=
  cylinderMean cuts R (witnessDigits s x i j)

theorem prefixThenDigits_before {k d : ℕ} (x : Prefix k d) (i j : Fin x.1.val)
    (D : Finset (Fin k)) (hji : j.val < i.val) :
    prefixThenDigits x i D (prefixColumn x j) = {x.2.get j} := by
  have hne : prefixColumn x j ≠ prefixColumn x i := by
    intro he
    have hv := congrArg (fun q : Fin d => q.val) he
    change j.val = i.val at hv
    omega
  unfold prefixThenDigits
  rw [Function.update_of_ne hne]
  simp [prefixDigits, takePrefix,
    prefixColumn, hji, RiffleShuffle.truncate, List.Vector.get,
    List.Vector.toList, Fin.cast]

theorem sideMean_eq_cylinderMean {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) :
    cylinderMean cuts R (prefixThenDigits x i (s.strictDigits (x.2.get i))) =
      sideMean s cuts R x i := by
  unfold cylinderMean
  rw [prefixThenDigits_mass cuts hn]
  cases s <;> unfold sideMean SuffixSide.strictDigits SuffixSide.test leftMean rightMean
  <;> simp only [leftProbability, rightProbability, mul_assoc]

/-- Restoring the omitted digit recovers the exact side-piece mean. -/
theorem witnessMean_mul_digit {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    (hji : j.val < i.val) :
    witnessMean cuts s R x i j * digitProbability cuts (prefixColumn x j) (x.2.get j) =
      sideMean s cuts R x i := by
  have hbase := prefixThenDigits_before x i j (s.strictDigits (x.2.get i)) hji
  have hrestore : Function.update (witnessDigits s x i j) (prefixColumn x j) {x.2.get j} =
      prefixThenDigits x i (s.strictDigits (x.2.get i)) := by
    funext t
    by_cases ht : t = prefixColumn x j
    · subst t
      simpa only [Function.update_self] using hbase.symm
    · simp only [witnessDigits, Function.update_of_ne ht]
  have hm := cylinderMass_update_univ cuts hn (witnessDigits s x i j) (prefixColumn x j)
    {x.2.get j} (by simp only [witnessDigits, Function.update_self])
  rw [hrestore] at hm
  have hs := sideMean_eq_cylinderMean cuts hn s R x i
  unfold cylinderMean at hs
  rw [hm] at hs
  simpa only [witnessMean, cylinderMean, digitProbability, allowedCount,
    Finset.sum_singleton, mul_assoc] using hs

theorem witnessMean_ge_sideMean {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    (hji : j.val < i.val) : sideMean s cuts R x i ≤ witnessMean cuts s R x i j := by
  have hw : 0 ≤ witnessMean cuts s R x i j :=
    mul_nonneg (Nat.cast_nonneg _) (cylinderMass_bounds cuts _).1
  have hd : digitProbability cuts (prefixColumn x j) (x.2.get j) ≤ 1 := by
    apply div_le_one_of_le₀
    · have hc : cuts.count (prefixColumn x j) (x.2.get j) ≤ n := by
        simpa only [allowedCount, Finset.sum_singleton] using
          allowedCount_le cuts (prefixColumn x j) {x.2.get j}
      exact_mod_cast hc
    · positivity
  rw [← witnessMean_mul_digit cuts hn s R x i j hji]
  nlinarith

end RiffleUpperV2.Anchor
