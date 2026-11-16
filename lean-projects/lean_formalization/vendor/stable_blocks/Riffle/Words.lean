import Riffle.Model
import Mathlib.Order.Interval.Set.OrdConnected

namespace Riffle

/-! Word, cylinder, and lexicographic foundations (frozen W01--W06). -/

theorem digit_prefix {x y : Word} (h : x <+: y) {i : ℕ} (hi : i < x.length) :
    digit x i = digit y i := by
  have hy : i < y.length := lt_of_lt_of_le hi h.length_le
  simp only [digit, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hy,
    Option.getD_some]
  exact h.getElem hi

theorem digit_take {x : Word} {m i : ℕ} (hi : i < m) :
    digit (x.take m) i = digit x i := by
  simp only [digit, List.getElem?_take_of_lt hi]

theorem legal_prefix {D : Model} {x y : Word} (hy : Legal D y) (h : x <+: y) :
    Legal D x := by
  refine ⟨h.length_le.trans hy.1, ?_⟩
  intro i hi
  rw [digit_prefix h hi]
  exact hy.2 i (hi.trans_le h.length_le)

theorem legal_take {D : Model} {x : Word} (hx : Legal D x) (m : ℕ) :
    Legal D (x.take m) := legal_prefix hx (List.take_prefix m x)

theorem prefixes_comparable {x y z : Word} (hx : x <+: z) (hy : y <+: z) :
    x <+: y ∨ y <+: x := List.prefix_or_prefix_of_prefix hx hy

theorem prefix_of_prefix_length_le {x y z : Word} (hx : x <+: z) (hy : y <+: z)
    (hlen : x.length ≤ y.length) : x <+: y :=
  List.prefix_of_prefix_length_le hx hy hlen

theorem parent_prefix (x : Word) : parent x <+: x := List.take_prefix _ _

theorem parent_length (x : Word) : (parent x).length = x.length - 1 := by
  simp [parent, Nat.min_eq_left (Nat.sub_le _ _)]

theorem parent_legal {D : Model} {x : Word} (hx : Legal D x) : Legal D (parent x) :=
  legal_prefix hx (parent_prefix x)

theorem prefix_parent {v x : Word} (h : v <+: x) (hlen : v.length < x.length) :
    v <+: parent x := by
  apply prefix_of_prefix_length_le h (parent_prefix x)
  rw [parent_length]
  omega

theorem join_properties {y z : Word} (h : y <+: z ∨ z <+: y) :
    y <+: join y z ∧ z <+: join y z ∧
    (join y z = y ∨ join y z = z) ∧ (join y z).length = max y.length z.length := by
  by_cases hlen : z.length ≤ y.length
  · rw [join, if_pos hlen]
    refine ⟨List.prefix_rfl, ?_, Or.inl rfl, (max_eq_left hlen).symm⟩
    rcases h with h | h
    · exact (h.eq_of_length_le hlen).symm ▸ List.prefix_rfl
    · exact h
  · rw [join, if_neg hlen]
    have hle : y.length ≤ z.length := by omega
    refine ⟨?_, List.prefix_rfl, Or.inr rfl, (max_eq_right hle).symm⟩
    rcases h with h | h
    · exact h
    · exact (h.eq_of_length_le hle).symm ▸ List.prefix_rfl

theorem pairDesc_eq {D : Model} {A : Setup D} {y z : Word}
    (hy : y ∈ Desc D A.w) (hz : z ∈ Desc D A.w) (hc : Compatible A y z) :
    pairDesc A y z = Desc D (join y z) := by
  rcases hc with ⟨u, hu⟩
  have hj := join_properties (prefixes_comparable hu.2.1 hu.2.2)
  have hwv : A.w <+: join y z := hy.2.trans hj.1
  ext x
  constructor
  · intro hx
    refine ⟨hx.1.1, ?_⟩
    rcases hj.2.2.1 with h | h
    · simpa [h] using hx.2.1
    · simpa [h] using hx.2.2
  · intro hx
    exact ⟨⟨hx.1, hwv.trans hx.2⟩, hj.1.trans hx.2, hj.2.1.trans hx.2⟩

theorem join_legal {D : Model} {y z : Word} (hy : Legal D y) (hz : Legal D z) :
    Legal D (join y z) := by
  unfold join
  split <;> assumption

theorem join_ambient {D : Model} {w y z : Word}
    (hy : y ∈ Desc D w) (hz : z ∈ Desc D w) : join y z ∈ Desc D w := by
  unfold join
  split <;> assumption

theorem terminal_iff_join_length {D : Model} {y z : Word}
    (hy : Legal D y) (hz : Legal D z) :
    Terminal D y z ↔ (join y z).length = D.K := by
  unfold Terminal join
  split <;> simp_all [Legal] <;> omega

theorem cylinder_mono {D : Model} {x y : Word} (h : x <+: y) :
    Cylinder D y ⊆ Cylinder D x := by
  intro ω hω
  exact ⟨hω.1, h.trans hω.2⟩

theorem cylinder_inter_eq_join {D : Model} {x y : Word} (h : x <+: y ∨ y <+: x) :
    Cylinder D x ∩ Cylinder D y = Cylinder D (join x y) := by
  have hj := join_properties h
  ext ω
  constructor
  · intro hω
    refine ⟨hω.1.1, ?_⟩
    rcases hj.2.2.1 with hv | hv
    · simpa [hv] using hω.1.2
    · simpa [hv] using hω.2.2
  · intro hω
    exact ⟨⟨hω.1, hj.1.trans hω.2⟩, ⟨hω.1, hj.2.1.trans hω.2⟩⟩

theorem cylinder_disjoint {D : Model} {x y : Word} (h : ¬ x <+: y ∧ ¬ y <+: x) :
    Disjoint (Cylinder D x) (Cylinder D y) := by
  apply Set.disjoint_left.mpr
  intro ω hx hy
  exact (prefixes_comparable hx.2 hy.2).elim h.1 h.2

theorem antichain_cylinder_disjoint {D : Model} {U : Set Word}
    (h : PrefixAntichain U) {x y : Word} (hx : x ∈ U) (hy : y ∈ U) (hne : x ≠ y) :
    Disjoint (Cylinder D x) (Cylinder D y) := by
  apply cylinder_disjoint
  exact ⟨fun hp => hne (h x hx y hy hp), fun hp => hne (h y hy x hx hp).symm⟩

theorem full_cylinder {D : Model} {x : Word} (hx : Full D x) :
    Cylinder D x = {x} := by
  ext ω
  constructor
  · intro hω
    exact (hω.2.eq_of_length (hx.2.trans hω.1.2.symm)).symm
  · intro hω
    subst ω
    exact ⟨hx, List.prefix_rfl⟩

theorem fullList_length {D : Model} (ω : FullIndex D) : (fullList ω).length = D.K := by
  simp [fullList]

theorem fullList_digit {D : Model} (ω : FullIndex D) {i : ℕ} (hi : i < D.K) :
    digit (fullList ω) i = (ω ⟨i, hi⟩).val := by
  simp [digit, fullList, hi]

theorem fullList_bounded {D : Model} (ω : FullIndex D) {i : ℕ}
    (hi : i < (fullList ω).length) : digit (fullList ω) i < D.k := by
  rw [fullList_length] at hi
  rw [fullList_digit ω hi]
  exact (ω ⟨i, hi⟩).isLt

theorem fullList_injective {D : Model} : Function.Injective (@fullList D) := by
  intro ω σ h
  funext i
  apply Fin.ext
  have hd := congrArg (fun x => digit x i.val) h
  simpa only [fullList_digit _ i.isLt] using hd

theorem fullList_existsUnique {D : Model} {x : Word} (hlen : x.length = D.K)
    (hb : ∀ i, i < x.length → digit x i < D.k) :
    ∃! ω : FullIndex D, fullList ω = x := by
  let ω : FullIndex D := fun i => ⟨digit x i, hb i (by simpa [hlen] using i.isLt)⟩
  have hω : fullList ω = x := by
    apply List.ext_getElem
    · simpa [fullList_length] using hlen.symm
    · intro i hi hj
      have hiK : i < D.K := by simpa [fullList_length] using hi
      have hd : digit (fullList ω) i = digit x i := by
        rw [fullList_digit ω hiK]
      simpa only [digit, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        Option.getD_some] using hd
  exact ⟨ω, hω, fun σ hσ => fullList_injective (hσ.trans hω.symm)⟩

theorem fullList_of_full {D : Model} {x : Word} (hx : Full D x) :
    ∃ ω : FullIndex D, fullList ω = x := by
  obtain ⟨ω, hω, _⟩ := fullList_existsUnique hx.2 (fun i hi => (hx.1.2 i hi).1)
  exact ⟨ω, hω⟩

theorem legal_append_singleton_iff {D : Model} {x : Word} (hx : Legal D x) (a : ℕ) :
    Legal D (x ++ [a]) ↔ x.length < D.K ∧ a < D.k ∧ 0 < D.n x.length a := by
  have hd : digit (x ++ [a]) x.length = a := by
    simp [digit, List.getElem?_append_right]
  constructor
  · intro h
    refine ⟨by simpa using h.1, ?_⟩
    have hl : x.length < (x ++ [a]).length := by simp
    simpa only [hd] using h.2 x.length hl
  · rintro ⟨hlen, ha, hn⟩
    refine ⟨by simpa using hlen, ?_⟩
    intro i hi
    by_cases hi' : i < x.length
    · rw [← digit_prefix (List.prefix_append x [a]) hi']
      exact hx.2 i hi'
    · have he : i = x.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      subst i
      simpa only [hd] using And.intro ha hn

theorem full_extension {D : Model} {x : Word} (hx : Legal D x) :
    ∃ ω, Full D ω ∧ x <+: ω := by
  have aux : ∀ m : ℕ, ∀ x : Word, D.K - x.length = m → Legal D x →
      ∃ ω, Full D ω ∧ x <+: ω := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hlen hx
      by_cases hf : x.length = D.K
      · exact ⟨x, ⟨hx, hf⟩, List.prefix_rfl⟩
      · have hlt : x.length < D.K := lt_of_le_of_ne hx.1 hf
        obtain ⟨a, ha, hn⟩ := exists_positive_digit D x.length hlt
        have hxa : Legal D (x ++ [a]) :=
          (legal_append_singleton_iff hx a).mpr ⟨hlt, ha, hn⟩
        have hdec : D.K - (x ++ [a]).length < m := by
          simp only [List.length_append, List.length_singleton]
          omega
        obtain ⟨ω, hω, hp⟩ := ih _ hdec (x ++ [a]) rfl hxa
        exact ⟨ω, hω, (List.prefix_append x [a]).trans hp⟩
  exact aux _ x rfl hx

theorem cylinder_nonempty_iff {D : Model} {x : Word} :
    (Cylinder D x).Nonempty ↔ Legal D x := by
  constructor
  · rintro ⟨ω, hω⟩
    exact legal_prefix hω.1.1 hω.2
  · intro hx
    exact full_extension hx

theorem compatible_iff_comparable {D : Model} {A : Setup D} {y z : Word}
    (hy : y ∈ Desc D A.w) (hz : z ∈ Desc D A.w) :
    Compatible A y z ↔ y <+: z ∨ z <+: y := by
  constructor
  · rintro ⟨x, hx⟩
    exact prefixes_comparable hx.2.1 hx.2.2
  · intro h
    have hj := join_properties h
    exact ⟨join y z, join_ambient hy hz, hj.1, hj.2.1⟩

theorem lexLE_iff_le {x y : Word} : LexLE x y ↔ x ≤ y := by
  rw [le_iff_eq_or_lt]
  rfl

theorem lexLE_take {x y : Word} (h : LexLE x y) (m : ℕ) :
    LexLE (x.take m) (y.take m) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · induction h generalizing m with
    | nil =>
      cases m with
      | zero => exact Or.inl rfl
      | succ m => exact Or.inr List.Lex.nil
    | rel h =>
      cases m with
      | zero => exact Or.inl rfl
      | succ m => exact Or.inr (List.Lex.rel h)
    | cons h ih =>
      cases m with
      | zero => exact Or.inl rfl
      | succ m =>
        rcases ih m with h | h
        · exact Or.inl (congrArg (List.cons _) h)
        · exact Or.inr (List.Lex.cons h)

theorem cylinder_convex {D : Model} {x a b c : Word}
    (ha : a ∈ Cylinder D x) (hc : c ∈ Cylinder D x) (hb : Full D b)
    (hab : LexLE a b) (hbc : LexLE b c) : b ∈ Cylinder D x := by
  have hleft := lexLE_take hab x.length
  have hright := lexLE_take hbc x.length
  rw [← List.prefix_iff_eq_take.mp ha.2] at hleft
  rw [← List.prefix_iff_eq_take.mp hc.2] at hright
  have htake : b.take x.length = x :=
    le_antisymm (lexLE_iff_le.mp hright) (lexLE_iff_le.mp hleft)
  exact ⟨hb, List.prefix_iff_eq_take.mpr htake.symm⟩

theorem lex_full_extensions {x y a b : Word} (hlen : x.length = y.length)
    (hxy : List.Lex (· < ·) x y) (ha : x <+: a) (hb : y <+: b) :
    List.Lex (· < ·) a b := by
  by_contra h
  have hba : b ≤ a := le_of_not_gt h
  have htake := lexLE_take (lexLE_iff_le.mpr hba) x.length
  have hax : a.take x.length = x := (List.prefix_iff_eq_take.mp ha).symm
  have hby : b.take x.length = y := by
    rw [hlen]
    exact (List.prefix_iff_eq_take.mp hb).symm
  rw [hax, hby] at htake
  exact not_lt_of_ge (lexLE_iff_le.mp htake) hxy

theorem rankSet_cylinder_convex {D : Model} {M : ℕ} {rows : Fin M → Word}
    (hfull : ∀ i, Full D (rows i)) (hsorted : SortedRows rows) (x : Word) :
    Set.OrdConnected (RankSet rows (Cylinder D x)) := by
  constructor
  intro i hi j hj q hq
  exact cylinder_convex hi hj (hfull q) (hsorted i q hq.1) (hsorted q j hq.2)

theorem rankSet_disjoint {M : ℕ} (rows : Fin M → Word) {E F : Set Word}
    (h : Disjoint E F) : Disjoint (RankSet rows E) (RankSet rows F) :=
  h.preimage rows

theorem rankSet_iUnion {M : ℕ} {ι : Sort*} (rows : Fin M → Word) (E : ι → Set Word) :
    RankSet rows (⋃ i, E i) = ⋃ i, RankSet rows (E i) := Set.preimage_iUnion

end Riffle
