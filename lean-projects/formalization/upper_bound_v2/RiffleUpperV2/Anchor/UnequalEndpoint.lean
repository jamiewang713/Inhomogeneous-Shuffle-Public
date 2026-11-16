import RiffleUpperV2.Anchor.UnequalHistory

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open TimeProfile

def unequalFixedRows {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :=
  R.filter (fun r => rowSlice ω r 0 j.val = x.2.toList.take j.val ∧
    ¬ s.test (rowSlice ω r (j.val+1) x.1.val) (x.2.toList.drop (j.val+1)) ∧
    (rowWord ω r).toList.take x.1.val < x.2.toList)

def unequalRandomRows {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :=
  R.filter (fun r => rowSlice ω r 0 j.val = x.2.toList.take j.val ∧
    s.test (rowSlice ω r (j.val+1) x.1.val) (x.2.toList.drop (j.val+1)) ∧
    sampleEntry ω r (prefixColumn x j) ∈ s.allowed (x.2.get j))

def unequalShift {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) : ℤ :=
  c₀ + (beforeRows R x j ω).card + (unequalFixedRows s R x j ω).card

private theorem unequal_row_count {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) (r : Fin n) :
    (if (rowWord ω r).toList.take x.1.val < x.2.toList then 1 else 0) =
    (if rowSlice ω r 0 j.val < x.2.toList.take j.val then 1 else 0) +
    (if rowSlice ω r 0 j.val = x.2.toList.take j.val ∧
      ¬ s.test (rowSlice ω r (j.val+1) x.1.val) (x.2.toList.drop (j.val+1)) ∧
      (rowWord ω r).toList.take x.1.val < x.2.toList then 1 else 0) +
    (if rowSlice ω r 0 j.val = x.2.toList.take j.val ∧
      s.test (rowSlice ω r (j.val+1) x.1.val) (x.2.toList.drop (j.val+1)) ∧
      sampleEntry ω r (prefixColumn x j) ∈ s.allowed (x.2.get j) then 1 else 0 : ℕ) := by
  have hp := row_precedes_split ω r x j
  by_cases ht : rowSlice ω r 0 j.val = x.2.toList.take j.val
  · have hn : ¬ rowSlice ω r 0 j.val < x.2.toList.take j.val := by rw [ht]; exact lt_irrefl _
    cases s
    · by_cases hs : rowSlice ω r (j.val+1) x.1.val < x.2.toList.drop (j.val+1)
      · have hp' : (rowWord ω r).toList.take x.1.val < x.2.toList ↔
            sampleEntry ω r (prefixColumn x j) ≤ x.2.get j := by
          rw [hp]
          simp only [lt_self_iff_false, hn, ht, hs, false_or, true_and, and_true, le_iff_lt_or_eq]
        simp only [SuffixSide.test, SuffixSide.allowed, Finset.mem_filter, Finset.mem_univ,
          true_and, lt_self_iff_false, ht, hn, hs, not_true_eq_false, false_and, if_false, Nat.zero_add,
          Nat.add_zero, hp']
      · simp only [SuffixSide.test, lt_self_iff_false, ht, hn, hs, not_false_eq_true, true_and, false_and,
          if_false, Nat.zero_add, Nat.add_zero]
    · by_cases hs : x.2.toList.drop (j.val+1) < rowSlice ω r (j.val+1) x.1.val
      · have hns : ¬ rowSlice ω r (j.val+1) x.1.val < x.2.toList.drop (j.val+1) := not_lt_of_gt hs
        have hp' : (rowWord ω r).toList.take x.1.val < x.2.toList ↔
            sampleEntry ω r (prefixColumn x j) < x.2.get j := by
          rw [hp]
          simp only [lt_self_iff_false, hn, ht, hns, false_or, true_and, and_false, or_false]
        simp only [SuffixSide.test, SuffixSide.allowed, Finset.mem_filter, Finset.mem_univ,
          true_and, lt_self_iff_false, ht, hn, hs, not_true_eq_false, false_and, if_false, Nat.zero_add,
          Nat.add_zero, hp']
      · simp only [SuffixSide.test, lt_self_iff_false, ht, hn, hs, not_false_eq_true, true_and, false_and,
          if_false, Nat.zero_add, Nat.add_zero]
  · have hp' : (rowWord ω r).toList.take x.1.val < x.2.toList ↔
        rowSlice ω r 0 j.val < x.2.toList.take j.val := by
      rw [hp]
      simp only [ht, false_and, or_false]
    simp only [ht, false_and, if_false, Nat.add_zero, hp']

/-- Both unequal orientations give one hypergeometric displacement. -/
theorem unequal_endpoint_shift {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d)
    (j : Fin x.1.val) (ω : Sample cuts) :
    lowerEndpoint c₀ R x ω = unequalShift s c₀ R x j ω + (unequalRandomRows s R x j ω).card ∧
    upperEndpoint c₀ R x ω = unequalShift s c₀ R x j ω + (unequalRandomRows s R x j ω).card +
      (prefixRows R x ω).card := by
  have hc : (R.filter (fun r => (rowWord ω r).toList.take x.1.val < x.2.toList)).card =
      (beforeRows R x j ω).card + (unequalFixedRows s R x j ω).card +
        (unequalRandomRows s R x j ω).card := by
    unfold beforeRows unequalFixedRows unequalRandomRows
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    exact unequal_row_count s x j ω r
  have hl : lowerEndpoint c₀ R x ω = unequalShift s c₀ R x j ω + (unequalRandomRows s R x j ω).card := by
    unfold lowerEndpoint unequalShift
    rw [hc]
    push_cast
    ring
  exact ⟨hl, by rw [upperEndpoint, hl]⟩

end RiffleUpperV2.Anchor
