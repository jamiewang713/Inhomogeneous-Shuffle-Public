import RiffleUpperV2.Anchor.CylinderExtension
import RiffleUpperV2.Anchor.EqualLaw

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric RiffleUpperV2.Localization

def nonEqualDigits {k : ℕ} (a : Fin k) := Finset.univ.filter (· ≠ a)

theorem nonEqualCount {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d) (a : Fin k) :
    allowedCount cuts j (nonEqualDigits a) + cuts.count j a = n := by
  have hs : nonEqualDigits a = Finset.univ.erase a := by
    ext b
    simp only [nonEqualDigits, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
  rw [allowedCount, hs, Finset.sum_erase_add _ _ (Finset.mem_univ a), cuts.sum_count]

theorem matchingBeforeRows_eq_prefixRows {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    matchingBeforeRows R x j ω = prefixRows R (takePrefix x j.val j.isLt.le) ω := by
  rfl

theorem equalSampleRows_eq_cylinder {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    equalSampleRows R x j ω = cylinderSet cuts R
      (prefixThenDigits x j (nonEqualDigits (x.2.get j))) ω := by
  rw [prefixThenDigits, cylinderSet_update_univ cuts R _ _ _ (prefixBefore_univ x j),
    ← prefixRows_eq_cylinderSet cuts, ← matchingBeforeRows_eq_prefixRows]
  apply Finset.ext
  intro r
  unfold equalSampleRows
  simp only [Finset.mem_sdiff, equalityRows_mem_iff, Finset.mem_filter,
    nonEqualDigits, Finset.mem_univ, true_and, sampleEntry]

def equalReserveRows {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :=
  (Finset.univ \ R) \ equalityRows (x.2.get j) (ω (prefixColumn x j))

theorem equalReserveRows_eq_cylinder {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    equalReserveRows R x j ω = cylinderSet cuts (Finset.univ \ R)
      (singleDigits (prefixColumn x j) (nonEqualDigits (x.2.get j))) ω := by
  rw [singleDigits_set]
  apply Finset.ext
  intro r
  unfold equalReserveRows
  simp only [Finset.mem_sdiff, equalityRows_mem_iff, Finset.mem_filter,
    nonEqualDigits, Finset.mem_univ, true_and, sampleEntry]

theorem equalReserveRows_eq_of_equalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
    equalReserveRows R x j ω = equalReserveRows R x j ω₀ := by
  unfold equalReserveRows
  rw [hf.2]

theorem equalSampleReserve_card_le {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    (equalSampleRows R x j ω).card + (equalReserveRows R x j ω).card ≤
      n - cuts.count (prefixColumn x j) (x.2.get j) := by
  have hdis : Disjoint (equalSampleRows R x j ω) (equalReserveRows R x j ω) := by
    apply Finset.disjoint_left.mpr
    intro r hb hc
    have hR : r ∈ R := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).1
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hc).1).2 hR
  have hsub : equalSampleRows R x j ω ∪ equalReserveRows R x j ω ⊆
      Finset.univ \ equalityRows (x.2.get j) (ω (prefixColumn x j)) := by
    intro r hr
    rcases Finset.mem_union.mp hr with hb | hc
    · exact equalSampleRows_subset R x j ω hb
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, (Finset.mem_sdiff.mp hc).2⟩
  have he := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, equalityRows_card] at he
  exact he

/-- Two genuine cylinder lower tails suffice for the equal-case good event. -/
def equalGood {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) : Prop :=
  cylinderMean cuts R (prefixThenDigits x j (nonEqualDigits (x.2.get j))) / 2 ≤
      (equalSampleRows R x j ω).card ∧
  cylinderMean cuts (Finset.univ \ R) (singleDigits (prefixColumn x j) (nonEqualDigits (x.2.get j))) / 2 ≤
      (equalReserveRows R x j ω).card

theorem equalGood_measurable {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
    equalGood cuts R x j ω ↔ equalGood cuts R x j ω₀ := by
  unfold equalGood
  rw [equalSampleRows_eq_of_equalReveal R x j hf, equalReserveRows_eq_of_equalReveal R x j hf]

end RiffleUpperV2.Anchor
