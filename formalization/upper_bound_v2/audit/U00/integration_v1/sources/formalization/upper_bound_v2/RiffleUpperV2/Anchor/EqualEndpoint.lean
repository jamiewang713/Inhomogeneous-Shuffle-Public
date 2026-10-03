import RiffleUpperV2.Anchor.RowSlices

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open TimeProfile

def beforeRows {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) : Finset (Fin n) :=
  R.filter (fun r => rowSlice ω r 0 j.val < x.2.toList.take j.val)

def matchingBeforeRows {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) : Finset (Fin n) :=
  R.filter (fun r => rowSlice ω r 0 j.val = x.2.toList.take j.val)

def equalSuffixRows {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) : Finset (Fin n) :=
  R.filter (fun r => rowSlice ω r 0 j.val = x.2.toList.take j.val ∧
    sampleEntry ω r (prefixColumn x j) = x.2.get j ∧
    rowSlice ω r (j.val+1) x.1.val < x.2.toList.drop (j.val+1))

def equalRandomRows {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) : Finset (Fin n) :=
  R.filter (fun r => rowSlice ω r 0 j.val = x.2.toList.take j.val ∧
    sampleEntry ω r (prefixColumn x j) < x.2.get j)

def equalShift {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ) (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) : ℤ :=
  c₀ + (beforeRows R x j ω).card + (equalSuffixRows R x j ω).card

/-- The equal-case endpoint decomposition is pointwise, with no probability
assumption and for every continuation length at or after the selected digit. -/
theorem equal_endpoint_shift {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    lowerEndpoint c₀ R x ω = equalShift c₀ R x j ω + (equalRandomRows R x j ω).card ∧
    upperEndpoint c₀ R x ω = equalShift c₀ R x j ω + (equalRandomRows R x j ω).card +
      (prefixRows R x ω).card := by
  have hc : (R.filter (fun r => (rowWord ω r).toList.take x.1.val < x.2.toList)).card =
      (beforeRows R x j ω).card + (equalSuffixRows R x j ω).card +
        (equalRandomRows R x j ω).card := by
    unfold beforeRows equalSuffixRows equalRandomRows
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have hsplit := row_precedes_split ω r x j
    by_cases hL : rowSlice ω r 0 j.val < x.2.toList.take j.val <;>
      by_cases hT : rowSlice ω r 0 j.val = x.2.toList.take j.val <;>
      by_cases hD : sampleEntry ω r (prefixColumn x j) < x.2.get j <;>
      by_cases hE : sampleEntry ω r (prefixColumn x j) = x.2.get j <;>
      by_cases hS : rowSlice ω r (j.val+1) x.1.val < x.2.toList.drop (j.val+1) <;>
      by_cases hP : (rowWord ω r).toList.take x.1.val < x.2.toList <;>
      simp_all only [hL, hT, hD, hE, hS, hP, true_or, false_or, or_true, or_false,
        true_and, false_and, and_true, and_false, lt_self_iff_false,
        not_true_eq_false, not_false_eq_true, if_true, if_false, Nat.add_zero, Nat.zero_add,
        true_iff, false_iff, iff_true, iff_false] <;> omega
  have hl : lowerEndpoint c₀ R x ω = equalShift c₀ R x j ω + (equalRandomRows R x j ω).card := by
    unfold lowerEndpoint equalShift
    rw [hc]
    push_cast
    ring
  exact ⟨hl, by rw [upperEndpoint, hl]⟩

end RiffleUpperV2.Anchor
