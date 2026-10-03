import RiffleUpperV2.Anchor.Main
import RiffleUpperV2.Localization.DensityAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

/-- Complete local future words, in the same order as rowWord.toList. -/
def historyWordRows {k n d : ℕ} (u : InternalHistory k n d) (w : Fin d → Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun r => u r = some w)

def historyLessRows {k n d : ℕ} (u : InternalHistory k n d) (w : Fin d → Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun r => ∃ q : Fin d → Fin k, u r = some q ∧ List.ofFn q < List.ofFn w)

def historySupport {k n d : ℕ} (u : InternalHistory k n d) : Finset (Fin n) :=
  Finset.univ.filter (fun r => u r ≠ none)

/-- Internal equal-word edge offsets, with empty/singleton word blocks contributing none. -/
def internalOffsets {k n d : ℕ} (u : InternalHistory k n d) : Finset ℤ :=
  Finset.univ.biUnion (fun w : Fin d → Fin k =>
    Finset.Ico ((historyLessRows u w).card : ℤ)
      ((historyLessRows u w).card + (historyWordRows u w).card - 1))

/-- Absolute integer left ranks of actual equal-word edges in the anchored block.
The arbitrary c₀ convention supports either zero-based or one-based ranks. -/
def anchoredEdges {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ) (R : Finset (Fin n))
    (x : Prefix k d) (ω : Sample cuts) : Finset ℤ :=
  (internalOffsets (internalHistory R x ω)).image (fun j => lowerEndpoint c₀ R x ω+j)

def anchoredEdgeProbability {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (m : ℤ) : ℝ :=
  probability (fixedCountPMF cuts) (fun ω => m ∈ anchoredEdges c₀ R x ω)

def anchoredDensity {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (slots : Finset ℤ) : ℝ :=
  ∑ m ∈ slots, (anchoredEdgeProbability cuts c₀ R x m)^2

theorem historyLess_disjoint_word {k n d : ℕ} (u : InternalHistory k n d) (w : Fin d → Fin k) :
    Disjoint (historyLessRows u w) (historyWordRows u w) := by
  apply Finset.disjoint_left.mpr
  intro r hl hw
  obtain ⟨q,hq,hlt⟩ := (Finset.mem_filter.mp hl).2
  have he := (Finset.mem_filter.mp hw).2
  have hqw : q = w := Option.some.inj (hq.symm.trans he)
  exact (ne_of_lt hlt) (congrArg List.ofFn hqw)

theorem historyLess_word_card_le {k n d : ℕ} (u : InternalHistory k n d) (w : Fin d → Fin k) :
    (historyLessRows u w).card + (historyWordRows u w).card ≤ n := by
  rw [← Finset.card_union_of_disjoint (historyLess_disjoint_word u w)]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

theorem internalOffsets_bounds {k n d : ℕ} (u : InternalHistory k n d) {j : ℤ}
    (hj : j ∈ internalOffsets u) : 0 ≤ j ∧ j < (n : ℤ)-1 := by
  obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hw
  have hc := historyLess_word_card_le u w
  have hc' : ((historyLessRows u w).card : ℤ) + (historyWordRows u w).card ≤ n := by exact_mod_cast hc
  have hp : (0:ℤ) ≤ (historyLessRows u w).card := Int.natCast_nonneg _
  omega

theorem historyWord_card_sum {k n d : ℕ} (u : InternalHistory k n d) :
    ∑ w : Fin d → Fin k, (historyWordRows u w).card = (historySupport u).card := by
  classical
  have he : (Finset.univ : Finset (Fin d → Fin k)).biUnion (historyWordRows u) = historySupport u := by
    ext r
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, historyWordRows,
      historySupport, Finset.mem_filter, true_and]
    exact ⟨by rintro ⟨w,hw⟩; simp [hw], fun h => Option.ne_none_iff_exists'.mp h⟩
  rw [← he, Finset.card_biUnion]
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro r ha hb
  exact hab (Option.some.inj ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2))

theorem internalOffsets_card_le_support {k n d : ℕ} (u : InternalHistory k n d) :
    (internalOffsets u).card ≤ (historySupport u).card := by
  rw [← historyWord_card_sum]
  apply (Finset.card_biUnion_le).trans
  apply Finset.sum_le_sum
  intro w _
  rw [Int.card_Ico]
  have h : (((historyLessRows u w).card : ℤ)+(historyWordRows u w).card-1) -
      (historyLessRows u w).card = (historyWordRows u w).card-1 := by omega
  rw [h]
  omega

theorem historySupport_internal {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (ω : Sample cuts) :
    historySupport (internalHistory R x ω) = Anchor.prefixRows R x ω := by
  ext r
  simp only [historySupport, Finset.mem_filter, Finset.mem_univ, true_and, internalHistory]
  by_cases hr : r ∈ Anchor.prefixRows R x ω <;> simp [hr]

theorem anchoredEdges_card {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    (anchoredEdges c₀ R x ω).card = (internalOffsets (internalHistory R x ω)).card := by
  unfold anchoredEdges
  apply Finset.card_image_of_injective
  intro i j he
  exact add_left_cancel he

theorem anchoredEdges_card_le_occupancy {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    (anchoredEdges c₀ R x ω).card ≤ (Anchor.prefixRows R x ω).card := by
  rw [anchoredEdges_card, ← historySupport_internal R x ω]
  exact internalOffsets_card_le_support _

end RiffleUpperV2.Localization
