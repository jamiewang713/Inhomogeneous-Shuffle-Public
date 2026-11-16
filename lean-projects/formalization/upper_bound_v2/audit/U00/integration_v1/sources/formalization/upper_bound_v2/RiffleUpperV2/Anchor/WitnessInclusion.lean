import RiffleUpperV2.Anchor.WitnessCylinder

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric

theorem witnessRows_coordinates {k n d : ℕ} (cuts : Cuts k n d)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    (hji : j.val < i.val) (ω : Sample cuts) (r : Fin n) (hr : r ∈ witnessRows cuts s R x i j ω) :
    r ∈ R ∧ (∀ t : Fin x.1.val, t.val < i.val → t ≠ j →
      sampleEntry ω r (prefixColumn x t) = x.2.get t) ∧
    s.test (sampleEntry ω r (prefixColumn x i)) (x.2.get i) := by
  have hh : r ∈ R ∧ ∀ t : Fin d, (ω t).val r ∈ witnessDigits s x i j t := by
    simpa only [witnessRows, cylinderSet, RiffleLowerV2.Thinning.intersectionWithin,
      Finset.mem_filter, Finset.mem_univ, true_and] using hr
  refine ⟨hh.1, ?_, ?_⟩
  · intro t hti htj
    have hne : prefixColumn x t ≠ prefixColumn x j := by
      intro he
      exact htj (Fin.ext (congrArg (fun q : Fin d => q.val) he))
    have he := hh.2 (prefixColumn x t)
    rw [witnessDigits, Function.update_of_ne hne, prefixThenDigits_before x i t _ hti,
      Finset.mem_singleton] at he
    exact he
  · have hne : prefixColumn x i ≠ prefixColumn x j := by
      intro he
      have hv := congrArg (fun q : Fin d => q.val) he
      change i.val = j.val at hv
      omega
    have he := hh.2 (prefixColumn x i)
    rw [witnessDigits, Function.update_of_ne hne, prefixThenDigits, Function.update_self] at he
    exact (Finset.mem_filter.mp he).2

/-- The strict source witness cylinder lies inside the enlarged full-suffix
sample set; all later continuation digits are unrestricted. -/
theorem witnessRows_subset_unequalSample {k n d : ℕ} (cuts : Cuts k n d)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    (hji : j.val < i.val) (ω : Sample cuts) :
    witnessRows cuts s R x i j ω ⊆ unequalSampleRows s R x j ω := by
  intro r hr
  have hc := witnessRows_coordinates cuts s R x i j hji ω r hr
  have hb : rowSlice ω r 0 j.val = x.2.toList.take j.val := by
    have hh := rowSlice_matches ω r x 0 j.val (Nat.zero_le _) j.isLt.le (by
      intro t _ ht
      exact hc.2.1 t (lt_trans ht hji) (by intro he; subst t; omega))
    simpa only [List.drop_zero] using hh
  have hs := rowSuffix_side_of_first_difference s ω r x (j.val+1) i (by omega)
    (by intro t ht hti; exact hc.2.1 t hti (by intro he; subst t; omega)) hc.2.2
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hc.1,hb⟩,hs⟩

theorem cylinderSet_other_invariant {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (D : Fin d → Finset (Fin k)) (j : Fin d) (hD : D j = Finset.univ)
    {ω₀ ω : Sample cuts} (hf : ∀ t : Fin d, t ≠ j → ω t = ω₀ t) :
    cylinderSet cuts R D ω = cylinderSet cuts R D ω₀ := by
  apply Finset.ext
  intro r
  simp only [cylinderSet, RiffleLowerV2.Thinning.intersectionWithin,
    Finset.mem_filter, Finset.mem_univ, true_and]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro t
  by_cases ht : t = j
  · subst t
    rw [hD]
    simp only [Finset.mem_univ]
  · rw [hf t ht]

theorem witnessRows_other_invariant {k n d : ℕ} (cuts : Cuts k n d)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    {ω₀ ω : Sample cuts} (hf : ∀ t : Fin d, t ≠ prefixColumn x j → ω t = ω₀ t) :
    witnessRows cuts s R x i j ω = witnessRows cuts s R x i j ω₀ := by
  exact cylinderSet_other_invariant cuts R _ (prefixColumn x j)
    (by simp only [witnessDigits, Function.update_self]) hf

end RiffleUpperV2.Anchor
