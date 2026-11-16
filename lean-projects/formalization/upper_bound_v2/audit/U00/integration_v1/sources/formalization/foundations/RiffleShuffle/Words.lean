import RiffleShuffle.Profiles

/-! Prefix and legality lemmas W01–W14 from the frozen contract. -/

namespace RiffleShuffle

variable {N k K m n r : ℕ}

/-- W01. -/
theorem prefix_refl (x : Word k m) : Prefix x x := List.prefix_refl _

/-- W02. -/
theorem prefix_trans {x : Word k m} {y : Word k n} {z : Word k r}
    (hxy : Prefix x y) (hyz : Prefix y z) : Prefix x z := hxy.trans hyz

/-- W03. -/
theorem prefix_length_le {x : Word k m} {y : Word k n}
    (hxy : Prefix x y) : m ≤ n := by
  simpa only [List.Vector.toList, x.2, y.2] using hxy.length_le

/-- W04. -/
theorem prefix_eq_of_length_eq {x y : Word k m} (hxy : Prefix x y) : x = y := by
  apply Subtype.ext
  exact hxy.eq_of_length (x.2.trans y.2.symm)

/-- W05. -/
theorem empty_prefix (x : Word k m) : Prefix (emptyWord k) x := List.nil_prefix

/-- W06. -/
theorem truncate_prefix (h : m ≤ n) (y : Word k n) : Prefix (truncate h y) y :=
  List.take_prefix _ _

/-- W07. -/
theorem prefix_iff_truncate {x : Word k m} {y : Word k n} (h : m ≤ n) :
    Prefix x y ↔ truncate h y = x := by
  constructor
  · intro hxy
    apply Subtype.ext
    simpa only [truncate, List.Vector.toList, x.2] using
      (List.prefix_iff_eq_take.mp hxy).symm
  · intro heq
    rw [← heq]
    exact truncate_prefix h y

/-- W08. -/
theorem prefix_comparable {x : Word k m} {y : Word k n} {z : Word k r}
    (hxz : Prefix x z) (hyz : Prefix y z) : Prefix x y ∨ Prefix y x :=
  List.prefix_or_prefix_of_prefix hxz hyz

/-- W09. -/
theorem take_lex_monotone (m : ℕ) : Monotone (List.take m : List (Fin k) → List (Fin k)) := by
  intro a b hab
  induction m generalizing a b with
  | zero => simp
  | succ m ih =>
    cases a with
    | nil =>
      change [] ≤ b.take (m + 1)
      rw [le_iff_eq_or_lt]
      cases b.take (m + 1) with
      | nil => exact Or.inl rfl
      | cons b bs => exact Or.inr List.Lex.nil
    | cons a as =>
      cases b with
      | nil =>
        rcases le_iff_eq_or_lt.mp hab with heq | hlt
        · cases heq
        · cases hlt
      | cons b bs =>
        simp only [List.take_succ_cons]
        rcases le_iff_eq_or_lt.mp hab with heq | hlt
        · injection heq with hab habs
          simp [hab, habs]
        · change List.Lex (· < ·) (a :: as) (b :: bs) at hlt
          cases hlt with
          | rel h => exact le_of_lt (List.Lex.rel h)
          | cons h => exact List.cons_le_cons _ (ih (le_of_lt h))

/-- W10. -/
theorem prefix_lex_convex {x a b c : List (Fin k)}
    (hab : a ≤ b) (hbc : b ≤ c) (hxa : x <+: a) (hxc : x <+: c) : x <+: b := by
  have ha : a.take x.length = x := (List.prefix_iff_eq_take.mp hxa).symm
  have hc : c.take x.length = x := (List.prefix_iff_eq_take.mp hxc).symm
  apply List.prefix_iff_eq_take.mpr
  apply le_antisymm
  · simpa only [ha] using take_lex_monotone x.length hab
  · simpa only [hc] using take_lex_monotone x.length hbc

/-- W11. -/
theorem legal_truncate {P : PileProfile N k K} {y : Word k n}
    (hy : Legal P y) (h : m ≤ n) : Legal P (truncate h y) := by
  refine ⟨h.trans hy.1, ?_⟩
  intro j
  convert hy.2 ⟨j.val, lt_of_lt_of_le j.isLt h⟩ using 1
  simp [truncate, List.Vector.get, List.Vector.toList, List.get_eq_getElem, Fin.cast]

/-- W12. -/
theorem legal_empty (P : PileProfile N k K) : Legal P (emptyWord k) := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro j
  exact Fin.elim0 j

/-- W13. -/
theorem legal_append_iff {P : PileProfile N k K} (x : Word k m) (a : Fin k) :
    Legal P (appendDigit x a) ↔ Legal P x ∧ m < K ∧ 0 < P.countAt m a := by
  constructor
  · intro h
    have hmK : m + 1 ≤ K := h.1
    have hlegal : Legal P x := by
      refine ⟨by omega, ?_⟩
      intro j
      convert h.2 ⟨j.val, by omega⟩ using 1
      simp [appendDigit, List.Vector.get, List.Vector.toList, List.get_eq_getElem, Fin.cast, j.isLt, x.2]
    refine ⟨hlegal, by omega, ?_⟩
    convert h.2 ⟨m, Nat.lt_succ_self m⟩ using 1
    simp [appendDigit, List.Vector.get, List.Vector.toList, List.get_eq_getElem, Fin.cast, x.2]
  · rintro ⟨hlegal, hm, ha⟩
    refine ⟨by omega, ?_⟩
    intro j
    by_cases hj : j.val < m
    · convert hlegal.2 ⟨j.val, hj⟩ using 1
      simp [appendDigit, List.Vector.get, List.Vector.toList, List.get_eq_getElem, Fin.cast, hj, x.2]
    · have hjeq : j.val = m := by omega
      simpa [appendDigit, List.Vector.get, List.Vector.toList, List.get_eq_getElem, Fin.cast, hjeq, x.2] using ha

/-- W14. -/
theorem legal_full_extension {P : PileProfile N k K} {x : Word k m}
    (hx : Legal P x) : ∃ y : Word k K, Legal P y ∧ Prefix x y := by
  classical
  let fill : Fin K → Fin k := fun j => Classical.choose (P.exists_positive_digit j.val j.isLt)
  have hfill : ∀ j : Fin K, 0 < P.countAt j.val (fill j) :=
    fun j => Classical.choose_spec (P.exists_positive_digit j.val j.isLt)
  let digits : Fin K → Fin k := fun j =>
    if hj : j.val < m then x.get ⟨j.val, hj⟩ else fill j
  let y : Word k K := List.Vector.ofFn digits
  refine ⟨y, ⟨le_rfl, ?_⟩, ?_⟩
  · intro j
    simp only [y, List.Vector.get_ofFn]
    by_cases hj : j.val < m
    · simpa only [digits, dif_pos hj] using hx.2 ⟨j.val, hj⟩
    · simpa only [digits, dif_neg hj] using hfill j
  · apply (prefix_iff_truncate hx.1).2
    apply List.Vector.ext
    intro j
    have hget : (truncate hx.1 y).get j = y.get ⟨j.val, lt_of_lt_of_le j.isLt hx.1⟩ := by
      simp [truncate, List.Vector.get, List.Vector.toList, List.get_eq_getElem, Fin.cast]
    rw [hget]
    simp [y, digits, j.isLt]

end RiffleShuffle
