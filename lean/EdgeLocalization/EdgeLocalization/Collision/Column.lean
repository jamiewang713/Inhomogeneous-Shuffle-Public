import EdgeLocalization.Collision.FiniteLaw
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Basic

/-! Prescribed columns and exact probabilities, frozen collision contract
C.D03–C.D05, C.D12, C.06–C.16 and C.40–C.42. -/

noncomputable section

namespace EdgeLocalization

open Finset

def FixedColumn (N k : ℕ) (n : Fin k → ℕ) : Type :=
  {c : Fin N → Fin k // ∀ a, (Finset.univ.filter (fun i => c i = a)).card = n a}

instance fixedColumnFintype (N k : ℕ) (n : Fin k → ℕ) :
    Fintype (FixedColumn N k n) := by
  classical
  unfold FixedColumn
  infer_instance

theorem fixedColumn_nonempty {N k : ℕ} (n : Fin k → ℕ)
    (h : ∑ a, n a = N) : Nonempty (FixedColumn N k n) := by
  classical
  let e : Fin N ≃ (Σ a : Fin k, Fin (n a)) :=
    Fintype.equivOfCardEq (by simpa using h.symm)
  let c : Fin N → Fin k := fun i => (e i).1
  refine ⟨⟨c, ?_⟩⟩
  intro a
  have hc : (Finset.univ : Finset (Fin (n a))).card =
      (Finset.univ.filter (fun i => c i = a)).card := by
    apply Finset.card_bij (fun t _ => e.symm ⟨a, t⟩)
    · intro t _
      simp [c]
    · intro t _ u _ htu
      simpa using e.symm.injective htu
    · intro i hi
      have hai : (e i).1 = a := (Finset.mem_filter.mp hi).2
      rcases he : e i with ⟨b, t⟩
      have hba : b = a := by simpa [he] using hai
      subst b
      refine ⟨t, Finset.mem_univ _, ?_⟩
      simpa [he] using e.symm_apply_apply i
  simpa using hc.symm

theorem pile_count_le_total {N k : ℕ} (n : Fin k → ℕ)
    (h : ∑ a, n a = N) (a : Fin k) : n a ≤ N := by
  calc
    n a ≤ ∑ b : Fin k, n b :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    _ = N := h

theorem column_count_reindex {N k : ℕ} (c : Fin N → Fin k)
    (π : Equiv.Perm (Fin N)) (a : Fin k) :
    (Finset.univ.filter (fun i => c (π i) = a)).card =
      (Finset.univ.filter (fun i => c i = a)).card := by
  classical
  apply Finset.card_bij (fun i _ => π i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact π.injective hij
  · intro j hj
    refine ⟨π.symm j, ?_, π.apply_symm_apply j⟩
    simpa using hj

def FixedColumn.reindex {N k : ℕ} (n : Fin k → ℕ)
    (π : Equiv.Perm (Fin N)) : FixedColumn N k n ≃ FixedColumn N k n where
  toFun c := ⟨fun i => c.val (π i), fun a =>
    (column_count_reindex c.val π a).trans (c.property a)⟩
  invFun c := ⟨fun i => c.val (π.symm i), fun a =>
    (column_count_reindex c.val π.symm a).trans (c.property a)⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    exact congrArg c.val (π.apply_symm_apply i)
  right_inv c := by
    apply Subtype.ext
    funext i
    exact congrArg c.val (π.symm_apply_apply i)

def columnLaw {N k : ℕ} (n : Fin k → ℕ)
    (h : ∑ a, n a = N) : FiniteLaw (FixedColumn N k n) := by
  letI := fixedColumn_nonempty n h
  exact FiniteLaw.uniform (FixedColumn N k n)

def singleFactor (N : ℕ) {k : ℕ} (n : Fin k → ℕ) (a : Fin k) : ℝ :=
  (n a : ℝ) / (N : ℝ)

def pairFactor (N : ℕ) {k : ℕ} (n : Fin k → ℕ) (a b : Fin k) : ℝ :=
  if a = b then ((n a * (n a - 1) : ℕ) : ℝ) /
    ((N : ℝ) * ((N - 1 : ℕ) : ℝ))
  else ((n a * n b : ℕ) : ℝ) /
    ((N : ℝ) * ((N - 1 : ℕ) : ℝ))

def coincidenceFactor (N : ℕ) {k : ℕ} (n : Fin k → ℕ) : ℝ :=
  ∑ a : Fin k, pairFactor N n a a

theorem ordered_distinct_pair_card (N : ℕ) :
    ((Finset.univ ×ˢ Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => p.1 ≠ p.2)).card = N * (N - 1) := by
  change (Finset.univ : Finset (Fin N)).offDiag.card = _
  simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]

theorem column_ordered_fiber_pair_card {N k : ℕ} {n : Fin k → ℕ}
    (c : FixedColumn N k n) (a b : Fin k) :
    ((Finset.univ ×ˢ Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => p.1 ≠ p.2 ∧ c.val p.1 = a ∧ c.val p.2 = b)).card =
      if a = b then n a * (n a - 1) else n a * n b := by
  classical
  by_cases hab : a = b
  · subst b
    let s := Finset.univ.filter (fun i => c.val i = a)
    have hs : ((Finset.univ ×ˢ Finset.univ : Finset (Fin N × Fin N)).filter
        (fun p => p.1 ≠ p.2 ∧ c.val p.1 = a ∧ c.val p.2 = a)) = s.offDiag := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and, Finset.mem_offDiag, s]
      tauto
    rw [hs, Finset.offDiag_card]
    simp [s, c.property a, Nat.mul_sub_left_distrib]
  · let s := Finset.univ.filter (fun i => c.val i = a)
    let t := Finset.univ.filter (fun i => c.val i = b)
    have hst : ((Finset.univ ×ˢ Finset.univ : Finset (Fin N × Fin N)).filter
        (fun p => p.1 ≠ p.2 ∧ c.val p.1 = a ∧ c.val p.2 = b)) = s ×ˢ t := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and, s, t]
      constructor
      · exact fun hp => hp.2
      · intro hp
        refine ⟨?_, hp⟩
        intro he
        apply hab
        exact hp.1.symm.trans ((congrArg c.val he).trans hp.2)
    rw [hst, Finset.card_product]
    simp only [s, t, c.property a, c.property b, if_neg hab]

theorem exists_perm_map_pair {N : ℕ} (i j i' j' : Fin N)
    (hij : i ≠ j) (hij' : i' ≠ j') :
    ∃ π : Equiv.Perm (Fin N), π i = i' ∧ π j = j' := by
  have hz : (Equiv.swap i i') j ≠ i' := by
    intro hz
    have he : (Equiv.swap i i') j = (Equiv.swap i i') i := by simpa using hz
    exact hij ((Equiv.swap i i').injective he).symm
  refine ⟨(Equiv.swap i i').trans (Equiv.swap ((Equiv.swap i i') j) j'), ?_, ?_⟩
  · change (Equiv.swap ((Equiv.swap i i') j) j') ((Equiv.swap i i') i) = i'
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hz.symm hij']
  · exact Equiv.swap_apply_left _ _

theorem column_probability_reindex {N k : ℕ} (n : Fin k → ℕ)
    (h : ∑ a, n a = N) (π : Equiv.Perm (Fin N))
    (A : FixedColumn N k n → Prop) :
    (columnLaw n h).probability (fun c => A (FixedColumn.reindex n π c)) =
      (columnLaw n h).probability A := by
  letI := fixedColumn_nonempty n h
  exact FiniteLaw.uniform_probability_reindex (FixedColumn.reindex n π) A

theorem column_one_probability {N k : ℕ} (n : Fin k → ℕ)
    (h : ∑ a, n a = N) (i : Fin N) (a : Fin k) :
    (columnLaw n h).probability (fun c => c.val i = a) = singleFactor N n a := by
  classical
  let w := columnLaw n h
  let p := w.probability (fun c => c.val i = a)
  let H : FixedColumn N k n → Finset (Fin N) :=
    fun c => Finset.univ.filter (fun j => c.val j = a)
  have hex (j : Fin N) : w.probability (fun c => c.val j = a) = p := by
    simpa [w, p, FixedColumn.reindex] using
      column_probability_reindex n h (Equiv.swap i j) (fun c => c.val i = a)
  have hsum : (N : ℝ) * p = (n a : ℝ) := by
    calc
      _ = ∑ j : Fin N, w.probability (fun c => c.val j = a) := by
        simp only [hex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ j : Fin N, w.probability (fun c => j ∈ H c) := by
        apply Finset.sum_congr rfl
        intro j _
        apply w.probability_congr
        intro c
        simp [H]
      _ = w.expectation (fun c => ((H c).card : ℝ)) :=
        w.sum_probabilities_eq_expected_card Finset.univ H (fun _ => Finset.filter_subset _ _)
      _ = w.expectation (fun _ => (n a : ℝ)) := by
        apply congrArg w.expectation
        funext c
        rw [show (H c).card = n a from c.property a]
      _ = _ := w.expectation_const _
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  apply (eq_div_iff hN).mpr
  simpa [p, singleFactor, mul_comm] using hsum

theorem column_two_probability {N k : ℕ} (n : Fin k → ℕ)
    (h : ∑ a, n a = N) (i j : Fin N) (hij : i ≠ j) (a b : Fin k) :
    (columnLaw n h).probability (fun c => c.val i = a ∧ c.val j = b) =
      pairFactor N n a b := by
  classical
  let w := columnLaw n h
  let p := w.probability (fun c => c.val i = a ∧ c.val j = b)
  let q : ℕ := if a = b then n a * (n a - 1) else n a * n b
  let s := (Finset.univ ×ˢ Finset.univ : Finset (Fin N × Fin N)).filter
    (fun r => r.1 ≠ r.2)
  let H : FixedColumn N k n → Finset (Fin N × Fin N) := fun c =>
    (Finset.univ ×ˢ Finset.univ).filter
      (fun r => r.1 ≠ r.2 ∧ c.val r.1 = a ∧ c.val r.2 = b)
  have hsub (c : FixedColumn N k n) : H c ⊆ s := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2.1⟩
  have hex (r : Fin N × Fin N) (hr : r ∈ s) :
      w.probability (fun c => c.val r.1 = a ∧ c.val r.2 = b) = p := by
    have hrne : r.1 ≠ r.2 := (Finset.mem_filter.mp hr).2
    obtain ⟨π, hπi, hπj⟩ := exists_perm_map_pair i j r.1 r.2 hij hrne
    simpa [w, p, FixedColumn.reindex, hπi, hπj] using
      column_probability_reindex n h π (fun c => c.val i = a ∧ c.val j = b)
  have hsum : ((N * (N - 1) : ℕ) : ℝ) * p = (q : ℝ) := by
    calc
      _ = ∑ r ∈ s, w.probability (fun c => c.val r.1 = a ∧ c.val r.2 = b) := by
        rw [show N * (N - 1) = s.card from (ordered_distinct_pair_card N).symm]
        calc
          _ = ∑ _r ∈ s, p := by simp
          _ = _ := Finset.sum_congr rfl (fun r hr => (hex r hr).symm)
      _ = ∑ r ∈ s, w.probability (fun c => r ∈ H c) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrne : r.1 ≠ r.2 := (Finset.mem_filter.mp hr).2
        apply w.probability_congr
        intro c
        simp [H, hrne]
      _ = w.expectation (fun c => ((H c).card : ℝ)) :=
        w.sum_probabilities_eq_expected_card s H hsub
      _ = w.expectation (fun _ => (q : ℝ)) := by
        apply congrArg w.expectation
        funext c
        rw [show (H c).card = q from column_ordered_fiber_pair_card c a b]
      _ = _ := w.expectation_const _
  have hN : 2 ≤ N := by
    by_contra hN
    apply hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hden : (N : ℝ) * ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (show N ≠ 0 by omega)
    · exact_mod_cast (show N - 1 ≠ 0 by omega)
  have heq : p = (q : ℝ) / ((N : ℝ) * ((N - 1 : ℕ) : ℝ)) := by
    apply (eq_div_iff hden).mpr
    simpa [Nat.cast_mul, mul_comm] using hsum
  by_cases hab : a = b <;> simpa [p, w, pairFactor, q, hab] using heq

theorem column_equal_probability {N k : ℕ} (n : Fin k → ℕ)
    (h : ∑ a, n a = N) (i j : Fin N) (hij : i ≠ j) :
    (columnLaw n h).probability (fun c => c.val i = c.val j) =
      coincidenceFactor N n := by
  classical
  let w := columnLaw n h
  let A : Fin k → FixedColumn N k n → Prop :=
    fun a c => c.val i = a ∧ c.val j = a
  calc
    _ = w.probability (fun c => ∃ a, A a c) := by
      apply w.probability_congr
      intro c
      constructor
      · intro hc
        exact ⟨c.val i, rfl, hc.symm⟩
      · rintro ⟨a, hia, hja⟩
        exact hia.trans hja.symm
    _ = ∑ a : Fin k, w.probability (A a) := by
      apply w.probability_disjoint_indexed_union
      intro c a b ha hb
      exact ha.1.symm.trans hb.1
    _ = coincidenceFactor N n := by
      apply Finset.sum_congr rfl
      intro a _
      exact column_two_probability n h i j hij a a

theorem column_zero_count {N k : ℕ} {n : Fin k → ℕ}
    (c : FixedColumn N k n) (a : Fin k) (ha : n a = 0) (i : Fin N) : c.val i ≠ a := by
  classical
  have hs : (Finset.univ.filter (fun j => c.val j = a)) = ∅ :=
    Finset.card_eq_zero.mp ((c.property a).trans ha)
  intro hi
  have hm : i ∈ Finset.univ.filter (fun j => c.val j = a) := by simp [hi]
  simp [hs] at hm

theorem singleFactor_nonneg (N : ℕ) {k : ℕ} (n : Fin k → ℕ) (a : Fin k) :
    0 ≤ singleFactor N n a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem pairFactor_nonneg (N : ℕ) {k : ℕ} (n : Fin k → ℕ) (a b : Fin k) :
    0 ≤ pairFactor N n a b := by
  unfold pairFactor
  split_ifs <;> positivity

theorem pairFactor_same_le_singleFactor_sq (N : ℕ) {k : ℕ} (n : Fin k → ℕ)
    (h : ∑ a, n a = N) (hN : 2 ≤ N) (a : Fin k) :
    pairFactor N n a a ≤ (singleFactor N n a)^2 := by
  by_cases ha : n a = 0
  · simp [pairFactor, singleFactor, ha]
  have hna : 1 ≤ n a := by omega
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNmR : 0 < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hnle : (n a : ℝ) ≤ (N : ℝ) := by exact_mod_cast pile_count_le_total n h a
  unfold pairFactor singleFactor
  rw [if_pos rfl, Nat.cast_mul, Nat.cast_sub hna,
    Nat.cast_sub (show 1 ≤ N by omega)]
  simp only [Nat.cast_one]
  rw [div_pow]
  apply (div_le_div_iff₀ (mul_pos hNR hNmR) (sq_pos_of_pos hNR)).mpr
  have hprod : 0 ≤ (N : ℝ) * (n a : ℝ) * ((N : ℝ) - (n a : ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sub_nonneg.mpr hnle)
  nlinarith

end EdgeLocalization
