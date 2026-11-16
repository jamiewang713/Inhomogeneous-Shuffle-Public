import Riffle.Boundary
import Riffle.Mass
import Riffle.Cost

namespace Riffle

/-! F04--F05: genuine crossings give positive fluctuation and no compatible pair is lost. -/

theorem crossing_replacement_mem {D : Model} {A : Setup D} {s : Side}
    {x ω : Word} {i : ℕ} (hx : x ∈ Desc D A.w) (hω : ω ∈ Cylinder D x)
    (hiw : A.w.length ≤ i) (hix : i < x.length) (hc : Cross A s x i) :
    let a := if s = .left then leftIndex A i else rightIndex A i
    Full D (ω.set i a) ∧ ω.set i a ∈ PieceEvent A s x i := by
  let a := if s = .left then leftIndex A i else rightIndex A i
  change Full D (ω.set i a) ∧ ω.set i a ∈ PieceEvent A s x i
  have hiK : i < D.K := hix.trans_le hx.1.1
  have hiω : i < ω.length := hix.trans_le hω.2.length_le
  have ha : a < D.k ∧ 0 < D.n i a := by
    cases s
    · simpa only [a, if_pos rfl] using leftIndex_legal A i hiK
    · simpa only [a, reduceCtorEq, ↓reduceIte] using rightIndex_legal A i hiK
  have hfull : Full D (ω.set i a) := by
    refine ⟨⟨by simpa using hω.1.1.1, ?_⟩, by simpa using hω.1.2⟩
    intro j hj
    have hjω : j < ω.length := by simpa using hj
    by_cases he : i = j
    · subst j
      simpa [digit, List.getElem?_set_self hiω] using ha
    · simpa only [digit, List.getElem?_set_ne he] using hω.1.1.2 j hjω
  have hw : A.w <+: ω.set i a := by
    apply List.prefix_iff_eq_take.mpr
    rw [List.take_set_of_le hiw]
    exact List.prefix_iff_eq_take.mp (hx.2.trans hω.2)
  let σ := (ω.set i a).take x.length
  have hσp : σ <+: ω.set i a := List.take_prefix _ _
  have hσlen : σ.length = x.length := by
    exact List.length_take_of_le (by simpa using hω.2.length_le)
  have hσw : A.w <+: σ :=
    prefix_of_prefix_length_le hw hσp (by rw [hσlen]; exact hx.2.length_le)
  have hσtake : σ.take i = x.take i := by
    have ht : x = ω.take x.length := List.prefix_iff_eq_take.mp hω.2
    simp only [σ, List.take_take, Nat.min_eq_left hix.le, List.take_set_of_le (le_refl i)]
    rw [ht, List.take_take, Nat.min_eq_left hix.le]
  have hσdigit : digit σ i = a := by
    rw [digit_take hix]
    simp [digit, List.getElem?_set_self hiω]
  refine ⟨hfull, ⟨σ, ⟨⟨legal_take hfull.1 _, hσw⟩, hσlen, hσtake, ?_⟩,
    hfull, hσp⟩⟩
  rw [hσdigit]
  cases s <;> simpa only [a, Cross, crossDigit, reduceCtorEq, ↓reduceIte] using hc

theorem crossing_piece_positive {D : Model} {A : Setup D} {s : Side}
    {x : Word} {i : ℕ} (hx : x ∈ Desc D A.w) (hiw : A.w.length ≤ i)
    (hix : i < x.length) (hc : Cross A s x i) :
    0 < expectedCount D (PieceEvent A s x i) := by
  obtain ⟨ω, hω, hp⟩ := full_extension hx.1
  have hm := crossing_replacement_mem hx (And.intro hω hp) hiw hix hc
  exact expectedCount_pos hm.1 hm.2

theorem rawPair_nonterminal_lengths {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) (hnt : ¬ Terminal D y z) :
    A.w.length < y.length ∧ A.w.length < z.length := by
  have hy : y.length ≠ D.K := fun h => hnt (Or.inl h)
  have hz : z.length ≠ D.K := fun h => hnt (Or.inr h)
  exact ⟨(boundary_nonterminal hp.1 hy).1, (boundary_nonterminal hp.2.1 hz).1⟩

theorem rawPair_sideMaximum_pos {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) (hnt : ¬ Terminal D y z) :
    0 < sideMaximum A .left (join y z) (join y z) ∧
    0 < sideMaximum A .right (join y z) (join y z) := by
  have hdesc := rawPair_join_desc hp
  have hj := rawPair_prefix_join hp
  have hy := boundary_nonterminal hp.1 (fun h => hnt (Or.inl h))
  have hz := boundary_nonterminal hp.2.1 (fun h => hnt (Or.inr h))
  constructor
  · have hiy : y.length - 1 < y.length := by omega
    have hiw : A.w.length ≤ y.length - 1 := by omega
    have hiv : y.length - 1 < (join y z).length := hiy.trans_le hj.1.length_le
    have hc : Cross A .left (join y z) (y.length - 1) := by
      unfold Cross
      rw [← digit_prefix hj.1 hiy]
      exact hy.2.1
    have he := crossing_piece_positive hdesc hiw hiv hc
    apply lt_of_lt_of_le he
    exact Finset.le_sup (f := fun i => expectedCount D (PieceEvent A .left (join y z) i))
      (Finset.mem_Ico.mpr ⟨hiw, hiv⟩)
  · have hiz : z.length - 1 < z.length := by omega
    have hiw : A.w.length ≤ z.length - 1 := by omega
    have hiv : z.length - 1 < (join y z).length := hiz.trans_le hj.2.length_le
    have hc : Cross A .right (join y z) (z.length - 1) := by
      unfold Cross
      rw [← digit_prefix hj.2 hiz]
      exact hz.2.1
    have he := crossing_piece_positive hdesc hiw hiv hc
    apply lt_of_lt_of_le he
    exact Finset.le_sup (f := fun i => expectedCount D (PieceEvent A .right (join y z) i))
      (Finset.mem_Ico.mpr ⟨hiw, hiv⟩)

theorem rawPair_sideFluctuation_pos {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) (hnt : ¬ Terminal D y z) :
    0 < sideFluctuation A .left (join y z) (join y z) ∧
    0 < sideFluctuation A .right (join y z) (join y z) := by
  have hs := rawPair_sideMaximum_pos hp hnt
  constructor
  · apply Real.sqrt_pos.mpr
    exact_mod_cast hs.1
  · apply Real.sqrt_pos.mpr
    exact_mod_cast hs.2

theorem rawPair_cF_ne_bot {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) (hnt : ¬ Terminal D y z) : cF A y z ≠ ⊥ := by
  have hs := rawPair_sideFluctuation_pos hp hnt
  simp only [cF, cFAt, extendedLog_of_pos D hs.1, extendedLog_of_pos D hs.2,
    ← WithBot.coe_min, ne_eq, WithBot.coe_ne_bot, not_false_eq_true]

theorem rawPair_retained {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) : Retained A y z := by
  refine ⟨hp.2.2, ?_⟩
  by_cases ht : Terminal D y z
  · exact Or.inl ht
  · exact Or.inr (rawPair_cF_ne_bot hp ht)

theorem admissiblePair_retained {D : Model} {A : Setup D} {y z : Word}
    (hp : AdmissiblePair A y z) : Retained A y z :=
  rawPair_retained (admissiblePair_rawPair hp)

theorem retained_nonterminal_finite {D : Model} {A : Setup D} {y z : Word}
    (hr : Retained A y z) (hnt : ¬ Terminal D y z) :
    ∃ f : ℝ, cF A y z = (f : WithBot ℝ) := by
  obtain ⟨f, hf⟩ := WithBot.ne_bot_iff_exists.mp (hr.2.resolve_left hnt)
  exact ⟨f, hf.symm⟩

end Riffle
