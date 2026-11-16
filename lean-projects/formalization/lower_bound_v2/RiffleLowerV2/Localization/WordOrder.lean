import Contracts.v1.WitnessGeometry
import RiffleLowerV2.Thinning.PrefixCoordinates

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization
open TimeProfile

/-- The first unequal coordinate determines the order of two maps on an ordered list. -/
theorem map_lt_map_iff {α β : Type*} [LinearOrder α] [LinearOrder β]
    (L : List α) (hL : L.Pairwise (· < ·)) (f g : α → β) :
    L.map f < L.map g ↔
      ∃ j ∈ L, f j < g j ∧ ∀ h ∈ L, h < j → f h = g h := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨ha, hL⟩ := List.pairwise_cons.mp hL
    rw [List.map_cons, List.map_cons]
    change List.Lex (· < ·) (f a :: L.map f) (g a :: L.map g) ↔ _
    rw [List.cons_lex_cons_iff]
    constructor
    · rintro (h | ⟨h, ht⟩)
      · refine ⟨a, by simp, h, ?_⟩
        intro j hj hja
        rcases List.mem_cons.mp hj with rfl | hj
        · exact (lt_irrefl _ hja).elim
        · exact (not_lt_of_gt (ha j hj) hja).elim
      · obtain ⟨j, hj, hjlt, hjpre⟩ := (ih hL).mp ht
        refine ⟨j, by simp [hj], hjlt, ?_⟩
        intro q hq hqj
        rcases List.mem_cons.mp hq with rfl | hq
        · exact h
        · exact hjpre q hq hqj
    · rintro ⟨j, hj, hjlt, hjpre⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Or.inl hjlt
      · refine Or.inr ⟨hjpre a (by simp) (ha j hj), (ih hL).mpr ?_⟩
        exact ⟨j, hj, hjlt, fun q hq hqj => hjpre q (by simp [hq]) hqj⟩

/-- Arbitrary selected coordinates are compared in their ambient column order. -/
theorem wordOnList_lt_iff {k K : ℕ} {I : Finset (Fin K)} (x y : WordOn k I) :
    wordOnList x < wordOnList y ↔
      ∃ j : I, x j < y j ∧ ∀ h : I, h < j → x h = y h := by
  have hs : (I.attach.sort).Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp I.attach.sortedLT_sort
  have h := map_lt_map_iff I.attach.sort hs x y
  simpa [wordOnList] using h

theorem wordOnList_injective {k K : ℕ} {I : Finset (Fin K)} :
    Function.Injective (wordOnList : WordOn k I → List (Fin k)) := by
  intro x y h
  funext j
  have he := List.map_inj_left.mp h
  exact he j (by simp)

/-- A single strictly increased digit strictly increases the selected-coordinate word. -/
theorem wordOnList_lt_of_single_change {k K : ℕ} {I : Finset (Fin K)}
    {x y : WordOn k I} (j : I) (hlt : x j < y j)
    (heq : ∀ h : I, h ≠ j → x h = y h) : wordOnList x < wordOnList y :=
  (wordOnList_lt_iff x y).mpr ⟨j, hlt, fun h hh => heq h (ne_of_lt hh)⟩

@[simp] theorem prefixAt_toList {k K : ℕ} (m : ℕ) (a : Word k K) (hm : m ≤ K) :
    (prefixAt m a).2.toList = a.toList.take m := by
  apply List.ext_getElem
  · simp [prefixAt, Nat.min_eq_left hm]
  · intro j hj hj'
    simp only [prefixAt, List.Vector.toList_ofFn, List.getElem_ofFn, List.getElem_take]
    simp only [List.Vector.get, List.get_eq_getElem, List.Vector.toList, Fin.val_cast]

theorem prefixAt_eq_of_get {k K m : ℕ} {a b : Word k K} (_hm : m ≤ K)
    (h : ∀ j : Fin K, j.val < m → a.get j = b.get j) :
    prefixAt m a = prefixAt m b := by
  unfold prefixAt
  congr 1
  apply List.Vector.ext
  intro j
  simp only [List.Vector.get_ofFn]
  exact h _ (lt_of_lt_of_le j.isLt (Nat.min_le_left _ _))

/-- Prefix products can be computed on the corresponding ambient column set. -/
theorem prefixMass_prefixAt_eq_prod {k N K : ℕ} (cuts : Cuts k N K)
    (m : ℕ) (a : Word k K) (_hm : m ≤ K) :
    prefixMass cuts (prefixAt m a) =
      ∏ j ∈ columnSet K 0 m, (cuts.count j (a.get j) : ℝ) / N := by
  unfold prefixMass prefixAt
  simp only [List.Vector.get_ofFn]
  apply Finset.prod_bij (fun j _ => (⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right m K)⟩ : Fin K))
  · intro j _
    simp only [columnSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Nat.zero_le _, lt_of_lt_of_le j.isLt (Nat.min_le_left m K)⟩
  · intro j _ q _ he
    exact Fin.ext (congrArg (fun i : Fin K => i.val) he)
  · intro j hj
    have hjm : j.val < min m K := lt_min
      (Finset.mem_filter.mp hj).2.2 j.isLt
    exact ⟨⟨j.val, hjm⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro j _
    rfl

end RiffleLowerV2.Localization
