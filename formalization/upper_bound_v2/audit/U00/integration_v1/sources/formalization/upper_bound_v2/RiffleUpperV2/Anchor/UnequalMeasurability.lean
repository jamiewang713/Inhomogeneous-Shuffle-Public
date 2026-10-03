import RiffleUpperV2.Anchor.UnequalEndpoint

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

theorem unequalExposed_mem_iff {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) (r : Fin n) :
    r ∈ unequalExposedRows s R x j ω ↔ r ∈ R ∧
      rowSlice ω r 0 j.val = x.2.toList.take j.val ∧
      ¬ s.test (rowSlice ω r (j.val+1) x.1.val) (x.2.toList.drop (j.val+1)) := by
  unfold unequalExposedRows unequalSampleRows matchingBeforeRows
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  tauto

theorem unequalFixedRows_eq_filter {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    unequalFixedRows s R x j ω = (unequalExposedRows s R x j ω).filter
      (fun r => (rowWord ω r).toList.take x.1.val < x.2.toList) := by
  apply Finset.ext
  intro r
  change (r ∈ R.filter (fun r => _)) ↔ r ∈ (unequalExposedRows s R x j ω).filter _
  simp only [Finset.mem_filter, unequalExposed_mem_iff]
  tauto

theorem unequalReveal_rowPrefix {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    {ω₀ ω : Sample cuts} (hf : unequalRevealFiber s R x j ω₀ ω) (r : Fin n)
    (hr : r ∈ unequalExposedRows s R x j ω₀) :
    (rowWord ω r).toList.take x.1.val = (rowWord ω₀ r).toList.take x.1.val := by
  have he : rowSlice ω r 0 x.1.val = rowSlice ω₀ r 0 x.1.val := by
    apply rowSlice_eq _ _ _ _ _ (Nat.zero_le _) (Nat.le_of_lt_succ x.1.isLt)
    intro t _ _
    by_cases ht : t = prefixColumn x j
    · subst t
      exact hf.2 r hr
    · exact congrArg (fun c => c.val r) (hf.1 t ht)
  simpa only [rowSlice, List.drop_zero] using he

theorem unequalFixedRows_eq_of_unequalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    {ω₀ ω : Sample cuts} (hf : unequalRevealFiber s R x j ω₀ ω) :
    unequalFixedRows s R x j ω = unequalFixedRows s R x j ω₀ := by
  rw [unequalFixedRows_eq_filter, unequalFixedRows_eq_filter,
    (other_unequalRows s R x j hf.1).2]
  apply Finset.filter_congr
  intro r hr
  exact Iff.of_eq (congrArg (fun u => u < x.2.toList) (unequalReveal_rowPrefix s R x j hf r hr))

theorem unequalShift_eq_of_unequalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    {ω₀ ω : Sample cuts} (hf : unequalRevealFiber s R x j ω₀ ω) :
    unequalShift s c₀ R x j ω = unequalShift s c₀ R x j ω₀ ∧
      (prefixRows R x ω).card = (prefixRows R x ω₀).card := by
  have hb : beforeRows R x j ω = beforeRows R x j ω₀ := by
    apply Finset.filter_congr
    intro r _
    exact Iff.of_eq (congrArg (fun u => u < x.2.toList.take j.val) (other_beforeSlice x j hf.1 r))
  exact ⟨by unfold unequalShift; rw [hb, unequalFixedRows_eq_of_unequalReveal s R x j hf],
    congrArg Finset.card (prefixRows_eq_of_unequalReveal s R x j hf)⟩

theorem unequalRandomRows_eq {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    unequalRandomRows s R x j ω = unequalSampleRows s R x j ω ∩
      residualAllowed (unequalExposedRows s R x j ω) (s.allowed (x.2.get j)) (ω (prefixColumn x j)) := by
  apply Finset.ext
  intro r
  unfold unequalRandomRows unequalSampleRows matchingBeforeRows residualAllowed
  change (r ∈ R.filter (fun r => _)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
    true_and, unequalExposed_mem_iff]
  change (r ∈ R ∧ _ ∧ _ ∧ sampleEntry ω r (prefixColumn x j) ∈ s.allowed (x.2.get j)) ↔ _
  unfold sampleEntry
  tauto

end RiffleUpperV2.Anchor
