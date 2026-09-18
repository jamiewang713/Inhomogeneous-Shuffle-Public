import RiffleLower.FiniteProbability
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact finite moments for independent randomizations of prescribed columns.
The definitions and every theorem are frozen in `FREEZE.md`, contract M01–M15. -/

open scoped BigOperators

namespace RiffleLower

noncomputable section

abbrev ColumnArray (N K k : ℕ) := Fin K → Fin N → Fin k

abbrev ColumnRandomness (N K : ℕ) := Fin K → Equiv.Perm (Fin N)

def columnCount {N K k : ℕ} (c : ColumnArray N K k) (t : Fin K) (a : Fin k) : ℕ :=
  (Finset.univ.filter fun i => c t i = a).card

def rowWord {N K k : ℕ} (c : ColumnArray N K k) (ω : ColumnRandomness N K)
    (i : Fin N) : Fin K → Fin k := fun t => c t (ω t i)

def wordCount {N K k : ℕ} (c : ColumnArray N K k) (w : Fin K → Fin k)
    (ω : ColumnRandomness N K) : ℕ :=
  (Finset.univ.filter fun i => rowWord c ω i = w).card

def wordMass {N K k : ℕ} (c : ColumnArray N K k) (w : Fin K → Fin k) : ℝ :=
  ∏ t, (columnCount c t (w t) : ℝ) / (N : ℝ)

def wordMean {N K k : ℕ} (c : ColumnArray N K k) (w : Fin K → Fin k) : ℝ :=
  (N : ℝ) * wordMass c w

def pairWordMass {N K k : ℕ} (c : ColumnArray N K k) (w : Fin K → Fin k) : ℝ :=
  ∏ t, ((columnCount c t (w t) : ℝ) * ((columnCount c t (w t) : ℝ) - 1)) /
    ((N : ℝ) * ((N : ℝ) - 1))

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

/-- M01: finite uniform expectations are invariant under equivalences. -/
theorem uniform_expect_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) (f : β → ℝ) :
    expect (uniformLaw α) (fun a => f (e a)) = expect (uniformLaw β) f := by
  rw [expect_uniform, expect_uniform, e.sum_comp, Fintype.card_congr e]

/-- M02: independent uniform coordinates factor products of functions exactly. -/
theorem uniform_pi_expect_prod {T : Type*} [Fintype T] {A : T → Type*}
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] (f : ∀ t, A t → ℝ) :
    expect (uniformLaw (∀ t, A t)) (fun ω => ∏ t, f t (ω t)) =
      ∏ t, expect (uniformLaw (A t)) (f t) := by
  classical
  simp_rw [expect_uniform]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Fintype.card_pi, Nat.cast_prod]

/-- M03: one specified position in a uniform permutation is uniform. -/
theorem uniform_perm_indicator {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (i : Fin N) :
    expect (uniformLaw (Equiv.Perm (Fin N)))
      (fun σ => if σ i ∈ S then 1 else 0) = (S.card : ℝ) / (N : ℝ) := by
  classical
  let P := uniformLaw (Equiv.Perm (Fin N))
  let b : Fin N → Equiv.Perm (Fin N) → ℝ := fun j σ => if σ j ∈ S then 1 else 0
  have hsym (j : Fin N) : expect P (b j) = expect P (b i) := by
    have h := uniform_expect_equiv (Equiv.mulRight (Equiv.swap i j)) (b i)
    simpa [P, b, Equiv.Perm.mul_apply] using h
  have htotal : (N : ℝ) * expect P (b i) = (S.card : ℝ) := by
    calc
      (N : ℝ) * expect P (b i) = ∑ j : Fin N, expect P (b j) := by
        simp_rw [hsym]
        simp
      _ = expect P (fun σ => ∑ j : Fin N, b j σ) := (expect_sum P Finset.univ b).symm
      _ = expect P (fun _ => (S.card : ℝ)) := by
        congr 1
        funext σ
        change (∑ j : Fin N, if σ j ∈ S then (1 : ℝ) else 0) = (S.card : ℝ)
        rw [Equiv.sum_comp σ (fun j => if j ∈ S then (1 : ℝ) else 0)]
        simp
      _ = (S.card : ℝ) := expect_const P _
  apply (eq_div_iff (show (N : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hN)).2
  simpa [P, b, mul_comm] using htotal

/-- M04: the exact two-position probability is sampling without replacement. -/
theorem uniform_perm_pair_indicator {N : ℕ} (hN : 2 ≤ N) (S : Finset (Fin N))
    (i j : Fin N) (hij : i ≠ j) :
    expect (uniformLaw (Equiv.Perm (Fin N)))
      (fun σ => (if σ i ∈ S then 1 else 0) * (if σ j ∈ S then 1 else 0)) =
      ((S.card : ℝ) * ((S.card : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  classical
  let P := uniformLaw (Equiv.Perm (Fin N))
  let b : Fin N → Equiv.Perm (Fin N) → ℝ := fun l σ => if σ l ∈ S then 1 else 0
  let q : Fin N → ℝ := fun l => expect P (fun σ => b i σ * b l σ)
  have hmean : expect P (b i) = (S.card : ℝ) / N := uniform_perm_indicator (by omega) S i
  have hdiag : q i = (S.card : ℝ) / N := by
    change expect P (fun σ => b i σ * b i σ) = _
    convert hmean using 1
    congr 1
    funext σ
    simp only [b]
    split_ifs <;> norm_num
  have hoff (l : Fin N) (hli : l ≠ i) : q l = q j := by
    have h := uniform_expect_equiv (Equiv.mulRight (Equiv.swap j l))
      (fun σ => b i σ * b j σ)
    have hfix : Equiv.swap j l i = i := Equiv.swap_apply_of_ne_of_ne hij hli.symm
    simpa [P, b, q, Equiv.Perm.mul_apply, hfix] using h
  have hsum : ∑ l : Fin N, q l = (S.card : ℝ) * ((S.card : ℝ) / N) := by
    calc
      (∑ l : Fin N, q l) = expect P (fun σ => ∑ l : Fin N, b i σ * b l σ) :=
        (expect_sum P Finset.univ (fun l σ => b i σ * b l σ)).symm
      _ = expect P (fun σ => b i σ * (S.card : ℝ)) := by
        congr 1
        funext σ
        rw [← Finset.mul_sum]
        congr 1
        change (∑ l : Fin N, if σ l ∈ S then (1 : ℝ) else 0) = _
        rw [Equiv.sum_comp σ (fun j => if j ∈ S then (1 : ℝ) else 0)]
        simp
      _ = (S.card : ℝ) * ((S.card : ℝ) / N) := by
        rw [expect_mul_const, hmean, mul_comm]
  have hsum' : ∑ l : Fin N, q l = ((N : ℝ) - 1) * q j + (S.card : ℝ) / N := by
    have hpoint (l : Fin N) : q l = q j + if l = i then (S.card : ℝ) / N - q j else 0 := by
      by_cases hli : l = i
      · subst l
        simp [hdiag]
      · simp [hli, hoff l hli]
    calc
      (∑ l : Fin N, q l) = ∑ l : Fin N,
          (q j + if l = i then (S.card : ℝ) / N - q j else 0) :=
        Finset.sum_congr rfl (fun l _ => hpoint l)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp
        ring
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  change q j = _
  apply (eq_div_iff (mul_ne_zero hN0 hN1)).2
  have hh := hsum.symm.trans hsum'
  field_simp [hN0] at hh
  nlinarith

/-- M05: a count and its second factorial power are sums of indicators. -/
theorem indicator_sum_factorial {I : Type*} [Fintype I] (B : I → Prop) :
    ((Finset.univ.filter B).card : ℝ) = (∑ i, if B i then 1 else 0) ∧
    ((Finset.univ.filter B).card : ℝ) * (((Finset.univ.filter B).card : ℝ) - 1) =
      ∑ i, ∑ j, if i ≠ j ∧ B i ∧ B j then 1 else 0 := by
  classical
  have hsum : ((Finset.univ.filter B).card : ℝ) = ∑ i, if B i then 1 else 0 := by
    simp
  refine ⟨hsum, ?_⟩
  have hpoint (i j : I) :
      (if i ≠ j ∧ B i ∧ B j then (1 : ℝ) else 0) =
        (if B i then 1 else 0) * (if B j then 1 else 0) -
          (if j = i then (if B i then 1 else 0) else 0) := by
    by_cases h : i = j
    · subst j
      by_cases hB : B i <;> simp [hB]
    · by_cases hi : B i <;> by_cases hj : B j <;> simp [h, Ne.symm h, hi, hj]
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul_sum]
  rw [← hsum]
  ring

/-- M06: every pile is a subset of the deck. -/
theorem columnCount_le {N K k : ℕ} (c : ColumnArray N K k) (t : Fin K) (a : Fin k) :
    columnCount c t a ≤ N := by
  unfold columnCount
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin N)

/-- M06: the column fibers partition the deck. -/
theorem sum_columnCount {N K k : ℕ} (c : ColumnArray N K k) (t : Fin K) :
    ∑ a, columnCount c t a = N := by
  classical
  simp only [columnCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- M07: complete-word probability lies in the unit interval, including zero piles. -/
theorem wordMass_bounds {N K k : ℕ} (c : ColumnArray N K k) (w : Fin K → Fin k)
    (hN : 0 < N) : 0 ≤ wordMass c w ∧ wordMass c w ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp (t : Fin K) : 0 ≤ (columnCount c t (w t) : ℝ) / N := by positivity
  refine ⟨Finset.prod_nonneg (fun t _ => hp t), ?_⟩
  apply Finset.prod_le_one (fun t _ => hp t)
  intro t _
  exact (div_le_one hNr).2 (by exact_mod_cast columnCount_le c t (w t))

/-- M07: the complete-word mean is between zero and the deck size. -/
theorem wordMean_bounds {N K k : ℕ} (c : ColumnArray N K k) (w : Fin K → Fin k)
    (hN : 0 < N) : 0 ≤ wordMean c w ∧ wordMean c w ≤ (N : ℝ) := by
  have h := wordMass_bounds c w hN
  unfold wordMean
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) h.1
  · nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- M08: a specified complete row has the product of its time-dependent digit probabilities. -/
theorem word_row_probability {N K k : ℕ} (c : ColumnArray N K k)
    (w : Fin K → Fin k) (hN : 0 < N) (i : Fin N) :
    prob (uniformLaw (ColumnRandomness N K))
      (Finset.univ.filter fun ω => rowWord c ω i = w) = wordMass c w := by
  classical
  let P := uniformLaw (ColumnRandomness N K)
  let b : Fin K → Equiv.Perm (Fin N) → ℝ :=
    fun t σ => if c t (σ i) = w t then 1 else 0
  have hind (ω : ColumnRandomness N K) :
      (if rowWord c ω i = w then (1 : ℝ) else 0) = ∏ t, b t (ω t) := by
    by_cases h : rowWord c ω i = w
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro t _
      simp [b, show c t (ω t i) = w t from congrFun h t]
    · rw [if_neg h]
      have h' : ¬ ∀ t, c t (ω t i) = w t := fun ht => h (funext ht)
      obtain ⟨t, ht⟩ := not_forall.mp h'
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [b, ht])
  calc
    prob P (Finset.univ.filter fun ω => rowWord c ω i = w) =
        expect P (fun ω => if rowWord c ω i = w then 1 else 0) := by
      simpa using (expect_indicator P (Finset.univ.filter fun ω => rowWord c ω i = w)).symm
    _ = expect P (fun ω => ∏ t, b t (ω t)) := by congr 1; funext ω; exact hind ω
    _ = ∏ t, expect (uniformLaw (Equiv.Perm (Fin N))) (b t) := by
      simp_rw [P, expect_uniform]
      rw [← Fintype.prod_sum, Finset.prod_div_distrib]
      simp [Fintype.card_pi, Nat.cast_prod]
    _ = wordMass c w := by
      apply Finset.prod_congr rfl
      intro t _
      simpa [b, columnCount] using
        uniform_perm_indicator hN (Finset.univ.filter fun a => c t a = w t) i

/-- M09: two distinct complete rows have the product of the exact one-column pair probabilities. -/
theorem word_two_rows_probability {N K k : ℕ} (c : ColumnArray N K k)
    (w : Fin K → Fin k) (hN : 2 ≤ N) (i j : Fin N) (hij : i ≠ j) :
    prob (uniformLaw (ColumnRandomness N K))
      (Finset.univ.filter fun ω => rowWord c ω i = w ∧ rowWord c ω j = w) =
      pairWordMass c w := by
  classical
  let P := uniformLaw (ColumnRandomness N K)
  let b : Fin K → Equiv.Perm (Fin N) → ℝ := fun t σ =>
    (if c t (σ i) = w t then 1 else 0) * (if c t (σ j) = w t then 1 else 0)
  have hind (ω : ColumnRandomness N K) :
      (if rowWord c ω i = w ∧ rowWord c ω j = w then (1 : ℝ) else 0) = ∏ t, b t (ω t) := by
    by_cases h : rowWord c ω i = w ∧ rowWord c ω j = w
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro t _
      simp [b, show c t (ω t i) = w t from congrFun h.1 t,
        show c t (ω t j) = w t from congrFun h.2 t]
    · rw [if_neg h]
      have h' : ¬ ∀ t, c t (ω t i) = w t ∧ c t (ω t j) = w t := by
        intro ht
        exact h ⟨funext (fun t => (ht t).1), funext (fun t => (ht t).2)⟩
      obtain ⟨t, ht⟩ := not_forall.mp h'
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      by_cases hi : c t (ω t i) = w t
      · have hj : c t (ω t j) ≠ w t := fun hj => ht ⟨hi, hj⟩
        simp [b, hj]
      · simp [b, hi]
  calc
    prob P (Finset.univ.filter fun ω => rowWord c ω i = w ∧ rowWord c ω j = w) =
        expect P (fun ω => if rowWord c ω i = w ∧ rowWord c ω j = w then 1 else 0) := by
      simpa using (expect_indicator P
        (Finset.univ.filter fun ω => rowWord c ω i = w ∧ rowWord c ω j = w)).symm
    _ = expect P (fun ω => ∏ t, b t (ω t)) := by congr 1; funext ω; exact hind ω
    _ = ∏ t, expect (uniformLaw (Equiv.Perm (Fin N))) (b t) := by
      simp_rw [P, expect_uniform]
      rw [← Fintype.prod_sum, Finset.prod_div_distrib]
      simp [Fintype.card_pi, Nat.cast_prod]
    _ = pairWordMass c w := by
      apply Finset.prod_congr rfl
      intro t _
      simpa [b, columnCount] using
        uniform_perm_pair_indicator hN (Finset.univ.filter fun a => c t a = w t) i j hij

/-- M10: the exact full-word occupancy mean. -/
theorem wordCount_expect {N K k : ℕ} (c : ColumnArray N K k)
    (w : Fin K → Fin k) (hN : 0 < N) :
    expect (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ)) =
      wordMean c w := by
  classical
  let P := uniformLaw (ColumnRandomness N K)
  have hrow (i : Fin N) :
      expect P (fun ω => if rowWord c ω i = w then 1 else 0) = wordMass c w := by
    have h := expect_indicator P (Finset.univ.filter fun ω => rowWord c ω i = w)
    simpa using h.trans (word_row_probability c w hN i)
  calc
    expect P (fun ω => (wordCount c w ω : ℝ)) =
        expect P (fun ω => ∑ i : Fin N, if rowWord c ω i = w then 1 else 0) := by
      congr 1
      funext ω
      simp [wordCount]
    _ = ∑ i : Fin N, expect P (fun ω => if rowWord c ω i = w then 1 else 0) :=
      expect_sum P Finset.univ _
    _ = wordMean c w := by simp_rw [hrow]; simp [wordMean]

/-- M11: the exact second factorial moment of complete-word occupancy. -/
theorem wordCount_factorial_second_moment {N K k : ℕ} (c : ColumnArray N K k)
    (w : Fin K → Fin k) (hN : 2 ≤ N) :
    expect (uniformLaw (ColumnRandomness N K))
      (fun ω => (wordCount c w ω : ℝ) * ((wordCount c w ω : ℝ) - 1)) =
      (N : ℝ) * ((N : ℝ) - 1) * pairWordMass c w := by
  classical
  let P := uniformLaw (ColumnRandomness N K)
  have hrow (i j : Fin N) :
      expect P (fun ω => if i ≠ j ∧ rowWord c ω i = w ∧ rowWord c ω j = w then 1 else 0) =
        if i ≠ j then pairWordMass c w else 0 := by
    by_cases hij : i = j
    · simp [hij]
    · have h := expect_indicator P
        (Finset.univ.filter fun ω => rowWord c ω i = w ∧ rowWord c ω j = w)
      simpa [hij] using h.trans (word_two_rows_probability c w hN i j hij)
  have hcount : (∑ i : Fin N, ∑ j : Fin N, if i ≠ j then (1 : ℝ) else 0) =
      (N : ℝ) * ((N : ℝ) - 1) := by
    simpa using (indicator_sum_factorial (fun _ : Fin N => True)).2.symm
  calc
    expect P (fun ω => (wordCount c w ω : ℝ) * ((wordCount c w ω : ℝ) - 1)) =
        expect P (fun ω => ∑ i : Fin N, ∑ j : Fin N,
          if i ≠ j ∧ rowWord c ω i = w ∧ rowWord c ω j = w then 1 else 0) := by
      congr 1
      funext ω
      have hs : (wordCount c w ω : ℝ) =
          ∑ i : Fin N, if rowWord c ω i = w then 1 else 0 := by simp [wordCount]
      have hp (i j : Fin N) :
          (if i ≠ j ∧ rowWord c ω i = w ∧ rowWord c ω j = w then (1 : ℝ) else 0) =
            (if rowWord c ω i = w then 1 else 0) * (if rowWord c ω j = w then 1 else 0) -
              (if j = i then (if rowWord c ω i = w then 1 else 0) else 0) := by
        by_cases hij : i = j
        · subst j
          by_cases hi : rowWord c ω i = w <;> simp [hi]
        · by_cases hi : rowWord c ω i = w <;>
            by_cases hj : rowWord c ω j = w <;> simp [hij, Ne.symm hij, hi, hj]
      simp_rw [hp, Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_mul_sum, ← hs]
      ring
    _ = ∑ i : Fin N, ∑ j : Fin N,
        expect P (fun ω => if i ≠ j ∧ rowWord c ω i = w ∧ rowWord c ω j = w then 1 else 0) := by
      rw [expect_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact expect_sum P Finset.univ _
    _ = ∑ i : Fin N, ∑ j : Fin N, if i ≠ j then pairWordMass c w else 0 := by
      simp_rw [hrow]
    _ = (∑ i : Fin N, ∑ j : Fin N, if i ≠ j then (1 : ℝ) else 0) * pairWordMass c w := by
      simp [Finset.sum_mul, ite_mul]
    _ = (N : ℝ) * ((N : ℝ) - 1) * pairWordMass c w := by rw [hcount]

/-- M12: two distinct rows have nonpositive covariance within one fixed-count column. -/
theorem one_column_pair_le_square {N d : ℕ} (hN : 2 ≤ N) (hd : d ≤ N) :
    0 ≤ (d : ℝ) * ((d : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) ∧
    (d : ℝ) * ((d : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) ≤
      ((d : ℝ) / (N : ℝ)) ^ 2 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hdr : (d : ℝ) ≤ N := by exact_mod_cast hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hnum : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    rcases d with _ | d
    · norm_num
    · have hd1 : (1 : ℝ) ≤ (d + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
      exact mul_nonneg (by positivity) (by linarith)
  refine ⟨div_nonneg hnum (le_of_lt (mul_pos hN0 hN1)), ?_⟩
  rw [div_pow]
  apply (div_le_div_iff₀ (mul_pos hN0 hN1) (sq_pos_of_pos hN0)).2
  have hprod : 0 ≤ (d : ℝ) * N * ((N : ℝ) - d) :=
    mul_nonneg (mul_nonneg hd0 hN0.le) (sub_nonneg.mpr hdr)
  nlinarith

/-- M13: the complete-word two-row probability is bounded by the squared one-row probability. -/
theorem pairWordMass_le_square {N K k : ℕ} (c : ColumnArray N K k)
    (w : Fin K → Fin k) (hN : 2 ≤ N) :
    0 ≤ pairWordMass c w ∧ pairWordMass c w ≤ (wordMass c w) ^ 2 := by
  have h t := one_column_pair_le_square hN (columnCount_le c t (w t))
  refine ⟨Finset.prod_nonneg (fun t _ => (h t).1), ?_⟩
  unfold pairWordMass wordMass
  rw [← Finset.prod_pow]
  exact Finset.prod_le_prod (fun t _ => (h t).1) (fun t _ => (h t).2)

/-- M14: complete-word occupancy has variance at most its exact mean. -/
theorem wordCount_variance_le_mean {N K k : ℕ} (c : ColumnArray N K k)
    (w : Fin K → Fin k) (hN : 2 ≤ N) :
    variance (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ)) ≤
      wordMean c w := by
  have hN0 : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcoef : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := mul_nonneg (by positivity) (by linarith)
  have hfac : expect (uniformLaw (ColumnRandomness N K))
      (fun ω => (wordCount c w ω : ℝ) * ((wordCount c w ω : ℝ) - 1)) ≤
      (expect (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ))) ^ 2 := by
    rw [wordCount_factorial_second_moment c w hN, wordCount_expect c w hN0]
    calc
      (N : ℝ) * ((N : ℝ) - 1) * pairWordMass c w ≤
          (N : ℝ) * ((N : ℝ) - 1) * (wordMass c w) ^ 2 :=
        mul_le_mul_of_nonneg_left (pairWordMass_le_square c w hN).2 hcoef
      _ ≤ (wordMean c w) ^ 2 := by
        unfold wordMean
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sq_nonneg (wordMass c w))]
  have h := variance_le_mean_of_factorial (uniformLaw (ColumnRandomness N K))
    (fun ω => (wordCount c w ω : ℝ)) hfac
  simpa only [wordCount_expect c w hN0] using h

/-- M15: a finite lower-tail estimate with no regularity or positive-pile assumption. -/
theorem wordCount_lower_tail {N K k : ℕ} (c : ColumnArray N K k)
    (w : Fin K → Fin k) (hN : 2 ≤ N) (m : ℕ) (hm : (m : ℝ) < wordMean c w) :
    1 - wordMean c w / (wordMean c w - (m : ℝ)) ^ 2 ≤
      prob (uniformLaw (ColumnRandomness N K))
        (Finset.univ.filter fun ω => m ≤ wordCount c w ω) := by
  have hN0 : 0 < N := by omega
  have h := lower_tail_from_variance (uniformLaw (ColumnRandomness N K))
    (fun ω => (wordCount c w ω : ℝ)) (m : ℝ)
    (by simpa only [wordCount_expect c w hN0] using hm)
    (by simpa only [wordCount_expect c w hN0] using wordCount_variance_le_mean c w hN)
  simpa only [wordCount_expect c w hN0, Nat.cast_le] using h

end

end RiffleLower
