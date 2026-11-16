import RiffleUpperV2.Anchor.UnequalDefinitions

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

/-- Full matching rows have equal suffix, so both unequal reveals expose their
selected digit. This includes immediate stopping at the join. -/
theorem prefixRows_subset_unequalExposed {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    (ω : Sample cuts) : prefixRows R x ω ⊆ unequalExposedRows s R x j ω := by
  intro r hr
  have hp : r ∈ R ∧ (rowWord ω r).toList.take x.1.val = x.2.toList :=
    Finset.mem_filter.mp hr
  have hb : rowSlice ω r 0 j.val = x.2.toList.take j.val := by
    have h := congrArg (List.take j.val) hp.2
    simpa only [rowSlice, List.drop_zero, List.take_take,
      Nat.min_eq_left j.isLt.le] using h
  have hs : rowSlice ω r (j.val+1) x.1.val = x.2.toList.drop (j.val+1) := by
    exact congrArg (List.drop (j.val+1)) hp.2
  have ht : r ∈ matchingBeforeRows R x j ω := Finset.mem_filter.mpr ⟨hp.1,hb⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨ht, ?_⟩
  intro hB
  have htest := (Finset.mem_filter.mp hB).2
  rw [hs] at htest
  cases s <;> exact (lt_irrefl _) htest

private theorem prefixRows_transport {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    {ω₀ ω : Sample cuts} (hf : unequalRevealFiber s R x j ω₀ ω) :
    prefixRows R x ω₀ ⊆ prefixRows R x ω := by
  intro r hr
  have hR := (Finset.mem_filter.mp hr).1
  apply Finset.mem_filter.mpr
  refine ⟨hR, (RiffleLowerV2.Thinning.prefix_coordinates_iff x ω r).mpr ?_⟩
  intro i
  have hcoord := prefixRows_coordinates R x ω₀ r hr i
  by_cases hi : i = j
  · subst i
    exact (hf.2 r (prefixRows_subset_unequalExposed s R x j ω₀ hr)).trans hcoord
  · have ht : prefixColumn x i ≠ prefixColumn x j := by
      intro he
      exact hi (Fin.ext (congrArg (fun q : Fin d => q.val) he))
    exact (congrArg (fun c => c.val r) (hf.1 (prefixColumn x i) ht)).trans hcoord

theorem unequalRevealFiber_symm {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    {ω₀ ω : Sample cuts} (hf : unequalRevealFiber s R x j ω₀ ω) :
    unequalRevealFiber s R x j ω ω₀ := by
  refine ⟨fun t ht => (hf.1 t ht).symm, ?_⟩
  intro r hr
  exact (hf.2 r ((other_unequalRows s R x j hf.1).2 ▸ hr)).symm

theorem prefixRows_eq_of_unequalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    {ω₀ ω : Sample cuts} (hf : unequalRevealFiber s R x j ω₀ ω) :
    prefixRows R x ω = prefixRows R x ω₀ := by
  exact Finset.Subset.antisymm
    (prefixRows_transport s R x j (unequalRevealFiber_symm s R x j hf))
    (prefixRows_transport s R x j hf)

theorem unequalReveal_refines_internal {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) :
    Refines (unequalRevealHistory (cuts := cuts) s R x j) (internalHistory R x) := by
  intro ω ω₀ he
  have hf := (unequalRevealHistory_eq_iff s R x j ω₀ ω).mp he
  have hr := prefixRows_eq_of_unequalReveal s R x j hf
  funext r
  by_cases h : r ∈ prefixRows R x ω₀
  · have h' : r ∈ prefixRows R x ω := hr.symm ▸ h
    simp only [internalHistory, h, h', if_true, Option.some.injEq]
    funext t
    by_cases ht : t = prefixColumn x j
    · subst t
      exact hf.2 r (prefixRows_subset_unequalExposed s R x j ω₀ h)
    · exact congrArg (fun c => c.val r) (hf.1 t ht)
  · have h' : r ∉ prefixRows R x ω := by simpa only [hr] using h
    simp only [internalHistory, h, h', if_false]

end RiffleUpperV2.Anchor
