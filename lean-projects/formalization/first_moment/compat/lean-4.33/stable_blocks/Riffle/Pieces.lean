import Riffle.Words

/-! Exact first-disagreement pieces and their continuation invariance.
The statements instantiate frozen F02–F03 and the W01 take identities. -/
namespace Riffle

theorem take_eq_of_prefix {x y : Word} (h : x <+: y) {m : ℕ}
    (hm : m ≤ x.length) : y.take m = x.take m := by
  have hx := List.prefix_iff_eq_take.mp h
  calc
    y.take m = (y.take x.length).take m := by
      rw [List.take_take, Nat.min_eq_left hm]
    _ = x.take m := by rw [← hx]

theorem piece_antichain {D : Model} (A : Setup D) (s : Side) (x : Word) (i : ℕ) :
    PrefixAntichain (Piece A s x i) := by
  intro σ hσ τ hτ hστ
  exact hστ.eq_of_length (hσ.2.1.trans hτ.2.1.symm)

theorem pieceEvent_iff {D : Model} {A : Setup D} (s : Side) {x ω : Word} {i : ℕ}
    (hx : x ∈ Desc D A.w) (_hiw : A.w.length ≤ i) (hix : i < x.length) :
    ω ∈ PieceEvent A s x i ↔
      ω ∈ Cylinder D A.w ∧ ω.take i = x.take i ∧
      (match s with | .left => digit ω i < digit x i
                    | .right => digit x i < digit ω i) := by
  constructor
  · rintro ⟨σ, hσ, hσω⟩
    have his : i < σ.length := by rw [hσ.2.1]; exact hix
    have ht : ω.take i = σ.take i := take_eq_of_prefix hσω.2 (by omega)
    refine ⟨⟨hσω.1, hσ.1.2.trans hσω.2⟩, ht.trans hσ.2.2.1, ?_⟩
    have hd := digit_prefix hσω.2 his
    cases s <;> simpa only [crossDigit, hd] using hσ.2.2.2
  · rintro ⟨hω, ht, hd⟩
    have hm : x.length ≤ ω.length := by have := hx.1.1; have := hω.1.2; omega
    have hlen : (ω.take x.length).length = x.length := List.length_take_of_le hm
    have hp : ω.take x.length <+: ω := List.take_prefix _ _
    have hw : A.w <+: ω.take x.length :=
      List.prefix_of_prefix_length_le hω.2 hp (by rw [hlen]; exact hx.2.length_le)
    refine ⟨ω.take x.length, ⟨⟨legal_take hω.1.1 _, hw⟩, hlen, ?_, ?_⟩,
      ⟨hω.1, hp⟩⟩
    · simpa only [List.take_take, Nat.min_eq_left (le_of_lt hix)] using ht
    · cases s <;> simpa only [crossDigit, digit_take hix] using hd

theorem pieceEvent_continuation {D : Model} {A : Setup D} (s : Side)
    {v x : Word} {i : ℕ} (hx : x ∈ Desc D A.w) (hvx : v <+: x)
    (hiw : A.w.length ≤ i) (hiv : i < v.length) :
    PieceEvent A s x i = PieceEvent A s v i := by
  have hv : v ∈ Desc D A.w := ⟨legal_prefix hx.1 hvx,
    List.prefix_of_prefix_length_le hx.2 hvx (by omega)⟩
  have hix : i < x.length := hiv.trans_le hvx.length_le
  have ht : x.take i = v.take i := take_eq_of_prefix hvx (le_of_lt hiv)
  have hd : digit v i = digit x i := digit_prefix hvx hiv
  ext ω
  rw [pieceEvent_iff s hx hiw hix, pieceEvent_iff s hv hiw hiv]
  rw [ht, hd]

theorem sideMaximum_continuation {D : Model} {A : Setup D} (s : Side)
    {v x : Word} (hx : x ∈ Desc D A.w) (hvx : v <+: x) :
    sideMaximum A s v x = sideMaximum A s v v := by
  classical
  unfold sideMaximum
  apply Finset.sup_congr rfl
  intro i hi
  have hb := Finset.mem_Ico.mp hi
  rw [pieceEvent_continuation s hx hvx hb.1 hb.2]

theorem sideFluctuation_continuation {D : Model} {A : Setup D} (s : Side)
    {v x : Word} (hx : x ∈ Desc D A.w) (hvx : v <+: x) :
    sideFluctuation A s v x = sideFluctuation A s v v := by
  rw [sideFluctuation, sideMaximum_continuation s hx hvx, sideFluctuation]

theorem cFAt_continuation {D : Model} {A : Setup D}
    {v x : Word} (hx : x ∈ Desc D A.w) (hvx : v <+: x) :
    cFAt A v x = cFAt A v v := by
  unfold cFAt
  rw [sideFluctuation_continuation .left hx hvx,
    sideFluctuation_continuation .right hx hvx]

theorem pieceEvent_disjoint_of_lt {D : Model} {A : Setup D} (s : Side)
    {x : Word} {i j : ℕ} (hx : x ∈ Desc D A.w)
    (hiw : A.w.length ≤ i) (hjw : A.w.length ≤ j)
    (hix : i < x.length) (hjx : j < x.length) (hij : i < j) :
    Disjoint (PieceEvent A s x i) (PieceEvent A s x j) := by
  apply Set.disjoint_left.mpr
  intro ω hωi hωj
  have hi := (pieceEvent_iff s hx hiw hix).mp hωi
  have hj := (pieceEvent_iff s hx hjw hjx).mp hωj
  have hd := congrArg (fun u => digit u i) hj.2.1
  simp only [digit_take hij] at hd
  cases s <;> simp only at hi
  · exact (ne_of_lt hi.2.2) hd
  · exact (ne_of_lt hi.2.2) hd.symm

theorem pieceEvent_disjoint {D : Model} {A : Setup D} (s : Side)
    {x : Word} {i j : ℕ} (hx : x ∈ Desc D A.w)
    (hiw : A.w.length ≤ i) (hjw : A.w.length ≤ j)
    (hix : i < x.length) (hjx : j < x.length) (hij : i ≠ j) :
    Disjoint (PieceEvent A s x i) (PieceEvent A s x j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact pieceEvent_disjoint_of_lt s hx hiw hjw hix hjx h
  · exact (pieceEvent_disjoint_of_lt s hx hjw hiw hjx hix h).symm

theorem lex_iff_first_difference {x y : Word} (hlen : x.length = y.length) :
    List.Lex (· < ·) x y ↔
      ∃ i, i < x.length ∧ x.take i = y.take i ∧ digit x i < digit y i := by
  induction x generalizing y with
  | nil =>
    have hy : y = [] := by simpa using hlen.symm
    subst y
    simp
  | cons a x ih =>
    cases y with
    | nil => simp at hlen
    | cons b y =>
      have htail : x.length = y.length := by simpa using hlen
      constructor
      · intro h
        cases h with
        | rel hab => exact ⟨0, by simp, by simp, by simpa [digit] using hab⟩
        | cons hxy =>
          obtain ⟨i, hi, ht, hd⟩ := (ih htail).mp hxy
          refine ⟨i + 1, by simpa using hi, ?_, ?_⟩
          · simpa using congrArg (List.cons a) ht
          · simpa [digit] using hd
      · rintro ⟨i, hi, ht, hd⟩
        cases i with
        | zero => exact List.Lex.rel (by simpa [digit] using hd)
        | succ i =>
          have ht' : a = b ∧ x.take i = y.take i := by simpa using ht
          rcases ht' with ⟨hab, htt⟩
          subst b
          apply List.Lex.cons
          apply (ih htail).mpr
          exact ⟨i, by simpa using hi, htt, by simpa [digit] using hd⟩

theorem pieceEvent_union {D : Model} {A : Setup D} (s : Side)
    {x : Word} (hx : x ∈ Desc D A.w) :
    {ω | ∃ i, A.w.length ≤ i ∧ i < x.length ∧ ω ∈ PieceEvent A s x i} =
    {ω | ω ∈ Cylinder D A.w ∧
      (match s with
       | .left => List.Lex (· < ·) (ω.take x.length) x
       | .right => List.Lex (· < ·) x (ω.take x.length))} := by
  ext ω
  have hlen (hω : ω ∈ Cylinder D A.w) : (ω.take x.length).length = x.length := by
    apply List.length_take_of_le
    have := hx.1.1
    have := hω.1.2
    omega
  cases s
  · constructor
    · rintro ⟨i, hiw, hix, hmem⟩
      have h := (pieceEvent_iff .left hx hiw hix).mp hmem
      refine ⟨h.1, (lex_iff_first_difference (hlen h.1)).mpr ?_⟩
      refine ⟨i, by rw [hlen h.1]; exact hix, ?_, ?_⟩
      · simpa only [List.take_take, Nat.min_eq_left (le_of_lt hix)] using h.2.1
      · simpa only [digit_take hix] using h.2.2
    · rintro ⟨hω, hlex⟩
      obtain ⟨i, hi, ht, hd⟩ := (lex_iff_first_difference (hlen hω)).mp hlex
      have hix : i < x.length := by rwa [hlen hω] at hi
      have ht' : ω.take i = x.take i := by
        simpa only [List.take_take, Nat.min_eq_left (le_of_lt hix)] using ht
      have hd' : digit ω i < digit x i := by simpa only [digit_take hix] using hd
      have hiw : A.w.length ≤ i := by
        by_contra hni
        have hiw' : i < A.w.length := by omega
        have hdx := digit_prefix hx.2 hiw'
        have hdω := digit_prefix hω.2 hiw'
        omega
      exact ⟨i, hiw, hix, (pieceEvent_iff .left hx hiw hix).mpr ⟨hω, ht', hd'⟩⟩
  · constructor
    · rintro ⟨i, hiw, hix, hmem⟩
      have h := (pieceEvent_iff .right hx hiw hix).mp hmem
      refine ⟨h.1, (lex_iff_first_difference (hlen h.1).symm).mpr ?_⟩
      refine ⟨i, hix, ?_, ?_⟩
      · simpa only [List.take_take, Nat.min_eq_left (le_of_lt hix)] using h.2.1.symm
      · simpa only [digit_take hix] using h.2.2
    · rintro ⟨hω, hlex⟩
      obtain ⟨i, hix, ht, hd⟩ := (lex_iff_first_difference (hlen hω).symm).mp hlex
      have ht' : ω.take i = x.take i := by
        simpa only [List.take_take, Nat.min_eq_left (le_of_lt hix)] using ht.symm
      have hd' : digit x i < digit ω i := by simpa only [digit_take hix] using hd
      have hiw : A.w.length ≤ i := by
        by_contra hni
        have hiw' : i < A.w.length := by omega
        have hdx := digit_prefix hx.2 hiw'
        have hdω := digit_prefix hω.2 hiw'
        omega
      exact ⟨i, hiw, hix, (pieceEvent_iff .right hx hiw hix).mpr ⟨hω, ht', hd'⟩⟩

end Riffle
