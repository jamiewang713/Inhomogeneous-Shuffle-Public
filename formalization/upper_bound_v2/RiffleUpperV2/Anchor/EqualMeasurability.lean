import RiffleUpperV2.Anchor.EqualEndpoint

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

theorem equalityRows_mem_iff {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (a : Fin k) (c : ColumnAssignments cuts j) (r : Fin n) :
    r ∈ equalityRows a c ↔ c.val r = a := by
  change r ∈ Finset.univ.filter (fun r => c.val r = a) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem equalReveal_digit_iff {k n d : ℕ} {cuts : Cuts k n d}
    {j : Fin d} {a : Fin k} {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber j a ω₀ ω) (r : Fin n) :
    sampleEntry ω r j = a ↔ sampleEntry ω₀ r j = a := by
  have he : (r ∈ equalityRows a (ω j)) ↔ (r ∈ equalityRows a (ω₀ j)) :=
    Iff.of_eq (congrArg (fun S : Finset (Fin n) => r ∈ S) hf.2)
  exact (equalityRows_mem_iff a (ω j) r).symm.trans
    (he.trans (equalityRows_mem_iff a (ω₀ j) r))

theorem equalReveal_beforeSlice {k n d : ℕ} {cuts : Cuts k n d}
    (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) (r : Fin n) :
    rowSlice ω r 0 j.val = rowSlice ω₀ r 0 j.val := by
  apply rowSlice_eq _ _ _ _ _ (Nat.zero_le _)
    (le_trans j.isLt.le (Nat.le_of_lt_succ x.1.isLt))
  intro t _ ht
  have hne : t ≠ prefixColumn x j := by
    intro he
    have hv := congrArg (fun t : Fin d => t.val) he
    change t.val = j.val at hv
    omega
  exact congrArg (fun c => c.val r) (hf.1 t hne)

theorem equalReveal_afterSlice {k n d : ℕ} {cuts : Cuts k n d}
    (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) (r : Fin n) :
    rowSlice ω r (j.val+1) x.1.val = rowSlice ω₀ r (j.val+1) x.1.val := by
  apply rowSlice_eq _ _ _ _ _ (Nat.succ_le_of_lt j.isLt) (Nat.le_of_lt_succ x.1.isLt)
  intro t ht _
  have hne : t ≠ prefixColumn x j := by
    intro he
    have hv := congrArg (fun t : Fin d => t.val) he
    change t.val = j.val at hv
    omega
  exact congrArg (fun c => c.val r) (hf.1 t hne)

theorem beforeRows_eq_of_equalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
    beforeRows R x j ω = beforeRows R x j ω₀ := by
  apply Finset.filter_congr
  intro r _
  exact Iff.of_eq (congrArg (fun u => u < x.2.toList.take j.val) (equalReveal_beforeSlice x j hf r))

theorem matchingBeforeRows_eq_of_equalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
    matchingBeforeRows R x j ω = matchingBeforeRows R x j ω₀ := by
  apply Finset.filter_congr
  intro r _
  exact Iff.of_eq (congrArg (fun u => u = x.2.toList.take j.val) (equalReveal_beforeSlice x j hf r))

theorem equalSuffixRows_eq_of_equalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
    equalSuffixRows R x j ω = equalSuffixRows R x j ω₀ := by
  apply Finset.filter_congr
  intro r _
  exact and_congr
    (Iff.of_eq (congrArg (fun u => u = x.2.toList.take j.val) (equalReveal_beforeSlice x j hf r)))
    (and_congr (equalReveal_digit_iff hf r)
      (Iff.of_eq (congrArg (fun u => u < x.2.toList.drop (j.val+1))
        (equalReveal_afterSlice x j hf r))))

/-- Both revealed shifts and the internal size are constant on the exact fine fiber. -/
theorem equalShift_eq_of_equalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
    equalShift c₀ R x j ω = equalShift c₀ R x j ω₀ ∧
      (prefixRows R x ω).card = (prefixRows R x ω₀).card := by
  constructor
  · unfold equalShift
    rw [beforeRows_eq_of_equalReveal R x j hf, equalSuffixRows_eq_of_equalReveal R x j hf]
  · exact congrArg Finset.card (prefixRows_eq_of_equalReveal R x j ω₀ ω hf)

end RiffleUpperV2.Anchor
