import RiffleUpperV2.Exploration.Positions
import RiffleUpperV2.Exploration.Histories

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir

def tupleCount {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) : ℕ :=
  (Finset.univ.filter fun r => f r = a).card

def observedCount {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α) (i : ℕ) (a : α) : ℕ :=
  (Finset.univ.filter fun r => r.val < i ∧ f r = a).card

private theorem cumulative_eq {α : Type*} [Fintype α] [LinearOrder α] [DecidableEq α] {n : ℕ}
    (f g : Fin n → α) (P : α → Prop)
    (hc : ∀ a, P a → tupleCount f a = tupleCount g a) :
    (Finset.univ.filter fun r => P (f r)).card =
      (Finset.univ.filter fun r => P (g r)).card := by
  have hf := Finset.sum_card_fiberwise_eq_card_filter
    (t := Finset.univ.filter P) (s := (Finset.univ : Finset (Fin n))) (g := f)
  have hg := Finset.sum_card_fiberwise_eq_card_filter
    (t := Finset.univ.filter P) (s := (Finset.univ : Finset (Fin n))) (g := g)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
  rw [← hf, ← hg]
  exact Finset.sum_congr rfl (fun a ha => hc a (Finset.mem_filter.mp ha).2)

private theorem observed_eq_full {α : Type*} [LinearOrder α] [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (hf : Monotone f) (j : Fin n) (a : α) (ha : a < f j) :
    observedCount f (j.val+1) a = tupleCount f a := by
  apply congrArg Finset.card
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro hr
    refine ⟨?_, hr⟩
    by_contra h
    have hjr : j ≤ r := by omega
    have := hf hjr
    rw [hr] at this
    exact (not_le.mpr ha) this

private theorem le_count_split {α : Type*} [LinearOrder α] [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (a : α) :
    (Finset.univ.filter fun r => f r ≤ a).card =
      (Finset.univ.filter fun r => f r < a).card + tupleCount f a := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun r => f r ≤ a) (p := fun r => f r < a)
  have h₁ : (Finset.univ.filter fun r => f r ≤ a).filter (fun r => f r < a) =
      Finset.univ.filter (fun r => f r < a) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    exact fun h => h.le
  have h₂ : (Finset.univ.filter fun r => f r ≤ a).filter (fun r => ¬ f r < a) =
      Finset.univ.filter (fun r => f r = a) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact le_antisymm_iff.symm
  rw [h₁, h₂] at h
  exact h.symm

private theorem initial_split {α : Type*} [LinearOrder α] [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (hf : Monotone f) (j : Fin n) :
    j.val+1 = (Finset.univ.filter fun r => f r < f j).card +
      observedCount f (j.val+1) (f j) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun r : Fin n => r.val < j.val+1) (p := fun r => f r < f j)
  have h₁ : (Finset.univ.filter fun r : Fin n => r.val < j.val+1).filter
      (fun r => f r < f j) = Finset.univ.filter (fun r => f r < f j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro hr
    by_contra hh
    exact (not_le.mpr hr) (hf (by omega))
  have h₂ : (Finset.univ.filter fun r : Fin n => r.val < j.val+1).filter
      (fun r => ¬ f r < f j) =
      Finset.univ.filter (fun r => r.val < j.val+1 ∧ f r = f j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hr, hh⟩
      exact ⟨hr, le_antisymm (hf (by omega)) (le_of_not_gt hh)⟩
    · rintro ⟨hr, hh⟩; exact ⟨hr, by simp [hh]⟩
  have hcard : (Finset.univ.filter fun r : Fin n => r.val < j.val+1).card = j.val+1 := by
    have hh : (Finset.univ.filter fun r : Fin n => r.val < j.val+1) = Finset.Iic j := by
      ext r; simp [Nat.lt_succ_iff]
    rw [hh, Fin.card_Iic]
  rw [h₁, h₂, hcard] at h
  exact h.symm

/-- A nonempty initial segment of a sorted tuple is exactly specified by all
strictly earlier multiplicities and the observed number of terminal copies.
The statement makes no probabilistic assumption. -/
theorem sorted_history_iff {α : Type*} [Fintype α] [LinearOrder α] [DecidableEq α] {n : ℕ}
    (f g : Fin n → α) (hf : Monotone f) (hg : Monotone g) (j : Fin n) :
    (∀ r : Fin n, r.val < j.val+1 → g r = f r) ↔
      (∀ a < f j, tupleCount g a = observedCount f (j.val+1) a) ∧
        observedCount f (j.val+1) (f j) ≤ tupleCount g (f j) := by
  constructor
  · intro he
    have hj : g j = f j := he j (by omega)
    have ho (a : α) : observedCount g (j.val+1) a = observedCount f (j.val+1) a := by
      apply congrArg Finset.card
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hr : r.val < j.val+1
      · rw [he r hr]
      · simp [hr]
    constructor
    · intro a ha
      rw [← observed_eq_full g hg j a (by rwa [hj]), ho]
    · rw [← ho]
      apply Finset.card_le_card
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.2⟩
  · rintro ⟨hc, hs⟩ r hr
    have hc' : ∀ a < f j, tupleCount g a = tupleCount f a := by
      intro a ha
      rw [hc a ha, observed_eq_full f hf j a ha]
    have hlt : (Finset.univ.filter fun r => g r < f j).card =
        (Finset.univ.filter fun r => f r < f j).card :=
      cumulative_eq g f (fun a => a < f j) hc'
    have hfr : f r ≤ f j := hf (by omega)
    have hlow : (Finset.univ.filter fun q => g q < f r).card =
        (Finset.univ.filter fun q => f q < f r).card :=
      cumulative_eq g f (fun a => a < f r) (fun a ha => hc' a (ha.trans_le hfr))
    apply le_antisymm
    · apply (Tuple.lt_card_le_iff_apply_le_of_monotone hg).mp
      by_cases heq : f r = f j
      · rw [heq, le_count_split, hlt]
        have hi := initial_split f hf j
        omega
      · have hstrict : f r < f j := lt_of_le_of_ne hfr heq
        have hle := cumulative_eq g f (fun a => a ≤ f r)
          (fun a ha => hc' a (ha.trans_lt hstrict))
        rw [hle]
        exact (Tuple.lt_card_le_iff_apply_le_of_monotone hf).mpr le_rfl
    · apply le_of_not_gt
      intro hh
      have hri := (Tuple.lt_card_lt_iff_apply_lt_of_monotone hg).mpr hh
      rw [hlow] at hri
      exact lt_irrefl _ ((Tuple.lt_card_lt_iff_apply_lt_of_monotone hf).mp hri)

end RiffleUpperV2.Reservoir
