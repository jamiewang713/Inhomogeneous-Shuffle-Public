import EdgeLocalization.Conditional.Split
import Mathlib.Data.Finset.Sort

namespace EdgeLocalization

/-- O.04: an arbitrary finite set has one increasing orientation per unordered pair. -/
theorem increasing_pairs_in_finset_card (s : Finset ℕ) :
    ((s ×ˢ s).filter (fun p => p.1 < p.2)).card = Nat.choose s.card 2 := by
  classical
  let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
  rw [← increasing_pair_card s.card]
  symm
  refine Finset.card_bij
    (fun p hp =>
      ((e ⟨p.1, Finset.mem_range.mp (Finset.mem_product.mp
        (Finset.mem_filter.mp hp).1).1⟩).val,
       (e ⟨p.2, Finset.mem_range.mp (Finset.mem_product.mp
        (Finset.mem_filter.mp hp).1).2⟩).val)) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpN, hpLt⟩
    rcases Finset.mem_product.mp hpN with ⟨hp1, hp2⟩
    have h1 := Finset.mem_range.mp hp1
    have h2 := Finset.mem_range.mp hp2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨(e ⟨p.1, h1⟩).property,
      (e ⟨p.2, h2⟩).property⟩, ?_⟩
    exact e.strictMono (show (⟨p.1, h1⟩ : Fin s.card) < ⟨p.2, h2⟩ from hpLt)
  · intro p hp q hq hpq
    apply Prod.ext
    · exact congrArg Fin.val (e.injective (Subtype.ext (congrArg Prod.fst hpq)))
    · exact congrArg Fin.val (e.injective (Subtype.ext (congrArg Prod.snd hpq)))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hpLt⟩
    rcases Finset.mem_product.mp hpS with ⟨hp1, hp2⟩
    let i := e.symm ⟨p.1, hp1⟩
    let j := e.symm ⟨p.2, hp2⟩
    have hij : i < j := e.symm.strictMono hpLt
    have hmem : (i.val, j.val) ∈
        ((Finset.range s.card) ×ˢ (Finset.range s.card)).filter (fun p => p.1 < p.2) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr i.isLt, Finset.mem_range.mpr j.isLt⟩, hij⟩
    refine ⟨(i.val, j.val), hmem, ?_⟩
    simp [i, j]

set_option backward.isDefEq.respectTransparency false in
/-- O.05: fixing the prefix array leaves the exact original-population tail collision factor. -/
theorem tail_expected_collisionPairs_given_prefix_array {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k)
    (p : FixedMatrix N (prefixCounts n hM)) :
    (matrixLaw (suffixCounts n hM)
      (fun j => hn ⟨M + j.val, by have hj := j.isLt; omega⟩)).expectation
      (fun t => ((collisionPairs N
        (sortedRows n ((splitMatrix N n hM).symm (p, t))) (prefixWord x)).card : ℝ)) =
      (Nat.choose (occupancyCount N
        (rawRows (prefixCounts n hM) p) (prefixWord x)) 2 : ℝ) *
        tailCollisionFactor N n M := by
  classical
  by_cases hN0 : N = 0
  · subst N
    simp [collisionPairs_zero, occupancyCount, occupied, FiniteLaw.expectation_const]
  by_cases hN1 : N = 1
  · subst N
    have hocc : occupancyCount 1 (rawRows (prefixCounts n hM) p) (prefixWord x) ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range 1)
    have hc : Nat.choose
        (occupancyCount 1 (rawRows (prefixCounts n hM) p) (prefixWord x)) 2 = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [collisionPairs_one, hc, FiniteLaw.expectation_const]
  let np := prefixCounts n hM
  let nt := suffixCounts n hM
  let hnt : ∀ j : Fin (K - M), ∑ a, nt j a = N :=
    fun j => hn ⟨M + j.val, by have hj := j.isLt; omega⟩
  let Wt := matrixLaw nt hnt
  let glue : FixedMatrix N nt → FixedMatrix N n :=
    fun t => (splitMatrix N n hM).symm (p, t)
  let s := occupied N (rawRows np p) (prefixWord x)
  let pairs := (s ×ˢ s).filter (fun ij => ij.1 < ij.2)
  let H : FixedMatrix N nt → Finset (ℕ × ℕ) :=
    fun t => collisionPairs N (rawRows n (glue t)) (prefixWord x)
  have hpre (t : FixedMatrix N nt) (j : Fin M) :
      (glue t) (Fin.castLE hM j) = p j := by
    exact congrArg (fun z : FixedMatrix N np × FixedMatrix N nt => z.1 j)
      ((splitMatrix N n hM).apply_symm_apply (p, t))
  have hsuf (t : FixedMatrix N nt) (j : Fin (K - M)) :
      (glue t) ⟨M + j.val, by have hj := j.isLt; omega⟩ = t j := by
    exact congrArg (fun z : FixedMatrix N np × FixedMatrix N nt => z.2 j)
      ((splitMatrix N n hM).apply_symm_apply (p, t))
  have hprefix (t : FixedMatrix N nt) (i : Fin N) :
      prefixWord x <+: rawRow n (glue t) i ↔ prefixWord x <+: rawRow np p i := by
    rw [prefixWord_prefix_rawRow_iff n hM x (glue t) i,
      prefixWord_prefix_rawRow_iff np (Nat.le_refl M) x p i]
    change (∀ j : Fin M, ((glue t) (Fin.castLE hM j)).val i = x j) ↔
      ∀ j : Fin M, (p j).val i = x j
    simp only [hpre]
  have hrows (t : FixedMatrix N nt) (i j : Fin N)
      (hi : prefixWord x <+: rawRow np p i)
      (hj : prefixWord x <+: rawRow np p j) :
      rawRow n (glue t) i = rawRow n (glue t) j ↔ rawRow nt t i = rawRow nt t j := by
    rw [rawRow_eq_iff n (glue t) i j, rawRow_eq_iff nt t i j]
    constructor
    · intro he a
      simpa only [hsuf] using he ⟨M + a.val, by have ha := a.isLt; omega⟩
    · intro he a
      by_cases ha : a.val < M
      · let b : Fin M := ⟨a.val, ha⟩
        have hb : Fin.castLE hM b = a := Fin.ext rfl
        have hi' : (p b).val i = x b :=
          (prefixWord_prefix_rawRow_iff np (Nat.le_refl M) x p i).mp hi b
        have hj' : (p b).val j = x b :=
          (prefixWord_prefix_rawRow_iff np (Nat.le_refl M) x p j).mp hj b
        rw [← hb, hpre]
        exact hi'.trans hj'.symm
      · let b : Fin (K - M) := ⟨a.val - M, by have haK := a.isLt; omega⟩
        have hb : (⟨M + b.val, by have hbK := b.isLt; omega⟩ : Fin K) = a := by
          apply Fin.ext
          dsimp [b]
          omega
        rw [← hb, hsuf]
        exact he b
  have hsmem (i : Fin N) :
      i.val ∈ s ↔ prefixWord x <+: rawRow np p i := by
    simp [s, occupied, rawRows, rowsOfLabels]
  have hsub (t : FixedMatrix N nt) : H t ⊆ pairs := by
    intro ij hij
    rcases Finset.mem_filter.mp hij with ⟨hijN, hijLt, hijEq, hijX⟩
    rcases Finset.mem_product.mp hijN with ⟨hiN, hjN⟩
    have hiN' := Finset.mem_range.mp hiN
    have hjN' := Finset.mem_range.mp hjN
    let i : Fin N := ⟨ij.1, hiN'⟩
    let j : Fin N := ⟨ij.2, hjN'⟩
    have hi : prefixWord x <+: rawRow n (glue t) i := by
      simpa [rawRows, rowsOfLabels, hiN', i] using hijX
    have he : rawRow n (glue t) i = rawRow n (glue t) j := by
      simpa [rawRows, rowsOfLabels, hiN', hjN', i, j] using hijEq
    have hj : prefixWord x <+: rawRow n (glue t) j := he ▸ hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(hsmem i).mpr ((hprefix t i).mp hi),
       (hsmem j).mpr ((hprefix t j).mp hj)⟩, hijLt⟩
  have hprob (ij : ℕ × ℕ) (hij : ij ∈ pairs) :
      Wt.probability (fun t => ij ∈ H t) = tailCollisionFactor N n M := by
    rcases Finset.mem_filter.mp hij with ⟨hijS, hijLt⟩
    rcases Finset.mem_product.mp hijS with ⟨hiS, hjS⟩
    have hiN := Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
    have hjN := Finset.mem_range.mp (Finset.mem_filter.mp hjS).1
    let i : Fin N := ⟨ij.1, hiN⟩
    let j : Fin N := ⟨ij.2, hjN⟩
    have hi : prefixWord x <+: rawRow np p i := (hsmem i).mp hiS
    have hj : prefixWord x <+: rawRow np p j := (hsmem j).mp hjS
    have hne : i ≠ j := fun he => (Nat.ne_of_lt hijLt) (congrArg Fin.val he)
    calc
      _ = Wt.probability (fun t => rawRow nt t i = rawRow nt t j) := by
        apply Wt.probability_congr
        intro t
        constructor
        · intro h
          have he : rawRow n (glue t) i = rawRow n (glue t) j := by
            simpa [rawRows, rowsOfLabels, hiN, hjN, i, j] using
              (Finset.mem_filter.mp h).2.2.1
          exact (hrows t i j hi hj).mp he
        · intro h
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr hiN, Finset.mem_range.mpr hjN⟩,
            hijLt, ?_, ?_⟩
          · simpa [rawRows, rowsOfLabels, hiN, hjN, i, j] using
              (hrows t i j hi hj).mpr h
          · simpa [rawRows, rowsOfLabels, hiN, i] using (hprefix t i).mpr hi
      _ = tailCollisionFactor N nt 0 := by
        simpa [Wt, prefixWord, prefixPairFactor] using
          matrix_pair_prefix_probability nt hnt (Nat.zero_le (K - M))
            (fun a : Fin 0 => Fin.elim0 a) i j hne
      _ = tailCollisionFactor N n M := tailCollisionFactor_suffix N n hM
  change Wt.expectation (fun t => ((collisionPairs N
    (sortedRows n (glue t)) (prefixWord x)).card : ℝ)) =
    (Nat.choose s.card 2 : ℝ) * tailCollisionFactor N n M
  calc
    _ = Wt.expectation (fun t => ((H t).card : ℝ)) := by
      apply congrArg Wt.expectation
      funext t
      rw [sorted_collisionPairs_card_eq_raw]
    _ = ∑ ij ∈ pairs, Wt.probability (fun t => ij ∈ H t) :=
      (Wt.sum_probabilities_eq_expected_card pairs H hsub).symm
    _ = ∑ _ij ∈ pairs, tailCollisionFactor N n M :=
      Finset.sum_congr rfl hprob
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, pairs, increasing_pairs_in_finset_card]

end EdgeLocalization
