import RiffleLowerV2.Localization.Endpoints.Coordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization
open TimeProfile

def relativeGreaterCount {k N K : ℕ} {cuts : Cuts k N K}
    (a : Word k K) (l m : ℕ) (x : WordOn k (columnSet K l m)) (omega : Sample cuts) : ℕ :=
  (Finset.univ.filter fun i : Fin N =>
    (rowWord omega i).toList.take l = a.toList.take l ∧
    wordOnList x < wordOnList (restrictWord (columnSet K l m) (rowWord omega i))).card

theorem relativeLowerCount_eq_side_sum {k N K l m : ℕ} {cuts : Cuts k N K}
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K)
    (x : WordOn k (columnSet K l m)) (omega : Sample cuts) :
    (relativeLowerCount a l m x omega : ℝ) =
      ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => d < x j),
        (prefixCount (sidePrefix a l m x j d) omega : ℝ) := by
  have hs := weighted_side_partition x
    (fun i : Fin N => restrictWord (columnSet K l m) (rowWord omega i))
    (fun i => (rowWord omega i).toList.take l = a.toList.take l)
    (fun _ => (1 : ℝ)) (fun d e : Fin k => d < e) (fun _ _ h => ne_of_lt h)
  simp_rw [← wordOnList_lt_iff] at hs
  simp_rw [← sidePrefix_coordinates a _ hlm hm x] at hs
  simp only [relativeLowerCount, prefixCount, Finset.sum_boole] at hs ⊢
  convert hs using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr
  · ext d
    simp
  · intro d _
    rfl

theorem relativeGreaterCount_eq_side_sum {k N K l m : ℕ} {cuts : Cuts k N K}
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K)
    (x : WordOn k (columnSet K l m)) (omega : Sample cuts) :
    (relativeGreaterCount a l m x omega : ℝ) =
      ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => x j < d),
        (prefixCount (sidePrefix a l m x j d) omega : ℝ) := by
  have hs := weighted_side_partition x
    (fun i : Fin N => restrictWord (columnSet K l m) (rowWord omega i))
    (fun i => (rowWord omega i).toList.take l = a.toList.take l)
    (fun _ => (1 : ℝ)) (fun d e : Fin k => e < d) (fun _ _ h => ne_of_gt h)
  have horder (y : WordOn k (columnSet K l m)) :
      (∃ j, x j < y j ∧ ∀ h, h < j → y h = x h) ↔ wordOnList x < wordOnList y := by
    rw [wordOnList_lt_iff]
    constructor <;> rintro ⟨j, hj, hpre⟩ <;>
      exact ⟨j, hj, fun h hh => (hpre h hh).symm⟩
  simp_rw [horder] at hs
  simp_rw [← sidePrefix_coordinates a _ hlm hm x] at hs
  simp only [relativeGreaterCount, prefixCount, Finset.sum_boole] at hs ⊢
  convert hs using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr
  · ext d
    simp
  · intro d _
    rfl

theorem relativeUpper_add_greater {k N K l m : ℕ} {cuts : Cuts k N K}
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K)
    (x : WordOn k (columnSet K l m)) (omega : Sample cuts) :
    (relativeUpperCount a l m x omega : ℝ) + relativeGreaterCount a l m x omega =
      (prefixCount (prefixAt l a) omega : ℝ) := by
  simp only [relativeUpperCount, relativeGreaterCount, prefixCount,
    show (prefixAt l a).1.val = l by simp [prefixAt, Nat.min_eq_left (hlm.trans hm)],
    prefixAt_toList l a (hlm.trans hm), ← Finset.sum_boole]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : (rowWord omega i).toList.take l = a.toList.take l
  · by_cases hx : wordOnList (restrictWord (columnSet K l m) (rowWord omega i)) ≤ wordOnList x
    · simp [ha, hx, not_lt_of_ge hx]
    · simp [ha, hx, lt_of_not_ge hx]
  · simp [ha]

end RiffleLowerV2.Localization
