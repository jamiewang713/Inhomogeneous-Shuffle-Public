import RiffleUpperV2.Anchor.Definitions

namespace RiffleUpperV2.Anchor

/-- The explicit three-way comparison at the next digit. -/
theorem list_cons_lt_iff {α : Type*} [LinearOrder α] (a b : α) (u v : List α) :
    a :: u < b :: v ↔ a < b ∨ (a = b ∧ u < v) := by
  constructor
  · intro h
    cases h with
    | rel h => exact Or.inl h
    | cons h => exact Or.inr ⟨rfl, h⟩
  · rintro (h | ⟨rfl,h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

/-- Equal-length prefixes decide order unless they agree exactly. -/
theorem list_append_lt_iff {α : Type*} [LinearOrder α]
    (u v s t : List α) (h : u.length = v.length) :
    u ++ s < v ++ t ↔ u < v ∨ (u = v ∧ s < t) := by
  induction u generalizing v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp h.symm
    subst v
    simp
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      have hlen : u.length = v.length := by simpa using h
      by_cases hab : a = b
      · subst b
        simp only [List.cons_append, list_cons_lt_iff, lt_self_iff_false,
          true_and, false_or, List.cons.injEq, ih v hlen]
      · simp only [List.cons_append, list_cons_lt_iff, hab, false_and,
          or_false, List.cons.injEq]

/-- Splitting at any available digit preserves the full lexicographic relation. -/
theorem list_split_lt_iff {α : Type*} [LinearOrder α]
    (u v : List α) (j : ℕ) (hju : j < u.length) (hjv : j < v.length) :
    u < v ↔ u.take j < v.take j ∨
      (u.take j = v.take j ∧ (u[j] < v[j] ∨
        (u[j] = v[j] ∧ u.drop (j+1) < v.drop (j+1)))) := by
  have he := list_append_lt_iff (u.take j) (v.take j) (u.drop j) (v.drop j)
    (by simp [List.length_take, Nat.min_eq_left hju.le, Nat.min_eq_left hjv.le])
  rw [List.take_append_drop, List.take_append_drop] at he
  rw [List.drop_eq_getElem_cons hju, List.drop_eq_getElem_cons hjv, list_cons_lt_iff] at he
  exact he

end RiffleUpperV2.Anchor
