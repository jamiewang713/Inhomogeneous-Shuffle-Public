import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic
import RiffleLower.FiniteProbability
import RiffleLower.Sorting

/-! Exact uniform-permutation estimates from frozen contract U01--U08. -/

noncomputable section

open scoped BigOperators
open Finset

namespace RiffleLower
attribute [local instance] Classical.propDecidable

def increasingAlong {N m : ℕ} (e : Fin m ↪ Fin N)
    (σ : Equiv.Perm (Fin N)) : Prop :=
  StrictMono (fun i => σ (e i))

def increasingAlongEvent {N m : ℕ} (e : Fin m ↪ Fin N) :
    Finset (Equiv.Perm (Fin N)) := by
  classical
  exact univ.filter (increasingAlong e)

def windowEmbedding (N m a : ℕ) (h : a + m ≤ N) : Fin m ↪ Fin N where
  toFun i := ⟨a + i.val, lt_of_lt_of_le (Nat.add_lt_add_left i.isLt a) h⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hij)

def windowEvent (N m a : ℕ) (h : a + m ≤ N) :
    Finset (Equiv.Perm (Fin N)) :=
  increasingAlongEvent (windowEmbedding N m a h)

def ascentEvent {N : ℕ} (i j : Fin N) : Finset (Equiv.Perm (Fin N)) :=
  univ.filter (fun σ => σ i < σ j)

def ascentCount {N : ℕ} (E : Finset (Fin N × Fin N))
    (σ : Equiv.Perm (Fin N)) : ℝ :=
  ∑ e ∈ E, if σ e.1 < σ e.2 then 1 else 0

/-- U01: an injective tuple has exactly one increasing reordering. -/
theorem unique_increasing_reordering {N m : ℕ} (f : Fin m → Fin N)
    (hf : Function.Injective f) :
    ∃! τ : Equiv.Perm (Fin m), StrictMono (f ∘ τ) := by
  refine ⟨Tuple.sort f, ?_, ?_⟩
  · exact (Tuple.monotone_sort f).strictMono_of_injective
      (hf.comp (Tuple.sort f).injective)
  · intro τ hτ
    apply Equiv.ext
    intro i
    apply hf
    exact congrFun (Tuple.unique_monotone hτ.monotone (Tuple.monotone_sort f)) i

/-- U02: reordering the sampled positions preserves the number of successful permutations. -/
theorem increasing_reordering_card {N m : ℕ} (e : Fin m ↪ Fin N)
    (τ : Equiv.Perm (Fin m)) :
    (univ.filter (fun σ : Equiv.Perm (Fin N) =>
      StrictMono (fun i => σ (e (τ i))))).card =
      (increasingAlongEvent e).card := by
  classical
  let er : Fin m ≃ Set.range e := Equiv.ofInjective e e.injective
  let p : Equiv.Perm (Fin N) := τ.extendDomain er
  have hp (i : Fin m) : p (e i) = e (τ i) := by
    exact τ.extendDomain_apply_image er i
  let b : Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N) :=
    { toFun := fun σ => p.trans σ
      invFun := fun σ => p.symm.trans σ
      left_inv := by intro σ; ext i; simp
      right_inv := by intro σ; ext i; simp }
  have hb (σ : Equiv.Perm (Fin N)) :
      StrictMono (fun i => σ (e (τ i))) ↔ increasingAlong e (b σ) := by
    simp only [increasingAlong, b, Equiv.coe_fn_mk, Equiv.trans_apply, hp]
  simpa only [increasingAlongEvent, Fintype.card_subtype] using
    Fintype.card_congr (b.subtypeEquiv hb)

/-- U03: exact factorial count of an increasing sample in prescribed positions. -/
theorem increasingAlong_card_mul_factorial {N m : ℕ} (e : Fin m ↪ Fin N) :
    (increasingAlongEvent e).card * m.factorial = N.factorial := by
  classical
  let q : Equiv.Perm (Fin N) → Equiv.Perm (Fin m) → ℕ :=
    fun σ τ => if StrictMono (fun i => σ (e (τ i))) then 1 else 0
  have hrow (σ : Equiv.Perm (Fin N)) : ∑ τ, q σ τ = 1 := by
    obtain ⟨τ, hτ, huniq⟩ :=
      unique_increasing_reordering (fun i => σ (e i)) (σ.injective.comp e.injective)
    rw [Finset.sum_eq_single τ]
    · simp only [q, Function.comp_def] at hτ ⊢
      simp [hτ]
    · intro b _ hb
      simp only [q, ite_eq_right_iff, one_ne_zero, imp_false]
      intro h
      exact hb (huniq b h)
    · simp
  have hcol (τ : Equiv.Perm (Fin m)) :
      ∑ σ, q σ τ = (increasingAlongEvent e).card := by
    simpa only [q, Finset.card_eq_sum_ones, Finset.sum_filter] using
      increasing_reordering_card e τ
  calc
    (increasingAlongEvent e).card * m.factorial =
        ∑ τ : Equiv.Perm (Fin m), (increasingAlongEvent e).card := by
          simp [Fintype.card_perm, Nat.mul_comm]
    _ = ∑ τ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin N), q σ τ := by
          simp_rw [hcol]
    _ = ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin m), q σ τ :=
          Finset.sum_comm
    _ = N.factorial := by simp_rw [hrow]; simp [Fintype.card_perm]

/-- U04: an arbitrary injectively sampled tuple has a uniform relative order. -/
theorem prob_increasingAlong {N m : ℕ} (e : Fin m ↪ Fin N) :
    prob (uniformLaw (Equiv.Perm (Fin N))) (increasingAlongEvent e) =
      1 / (m.factorial : ℝ) := by
  rw [prob_uniform]
  simp only [Fintype.card_perm, Fintype.card_fin]
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (increasingAlong_card_mul_factorial e)
  simp only [Nat.cast_mul] at hc
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))).mpr
  simpa using hc

/-- U05: a sampled increasing window is exactly the fixed-start run predicate. -/
theorem mem_windowEvent_iff {N m a : ℕ} (h : a + m ≤ N)
    (σ : Equiv.Perm (Fin N)) :
    σ ∈ windowEvent N m a h ↔
      ∀ i j : Fin N, a ≤ i.val → j.val < a + m → i < j → σ i < σ j := by
  classical
  change σ ∈ univ.filter (increasingAlong (windowEmbedding N m a h)) ↔ _
  simp only [mem_filter, mem_univ, true_and, increasingAlong]
  constructor
  · intro hs i j hi hj hij
    let ii : Fin m := ⟨i.val - a, by have := i.isLt; have := j.isLt; omega⟩
    let jj : Fin m := ⟨j.val - a, by have := i.isLt; have := j.isLt; omega⟩
    have he_i : windowEmbedding N m a h ii = i := by
      apply Fin.ext
      dsimp [windowEmbedding, ii]
      omega
    have he_j : windowEmbedding N m a h jj = j := by
      apply Fin.ext
      dsimp [windowEmbedding, jj]
      omega
    rw [← he_i, ← he_j]
    apply hs
    change i.val - a < j.val - a
    omega
  · intro hs i j hij
    apply hs
    · change a ≤ a + i.val
      omega
    · change a + j.val < a + m
      exact Nat.add_lt_add_left j.isLt a
    · change a + i.val < a + j.val
      exact Nat.add_lt_add_left hij a

/-- U05: all admissible starts give exactly the observable increasing-run event. -/
theorem increasingRun_eq_union {N m : ℕ} (hm : m ≤ N) :
    (univ.filter (fun σ : Equiv.Perm (Fin N) => HasIncreasingRun σ m)) =
      unionEvents (fun a : Fin (N - m + 1) =>
        windowEvent N m a.val (by have := a.isLt; omega)) univ := by
  classical
  ext σ
  simp only [mem_filter, mem_univ, true_and, unionEvents, mem_biUnion]
  constructor
  · rintro ⟨a, ha, hs⟩
    have ha' : a < N - m + 1 := by omega
    refine ⟨⟨a, ha'⟩, ?_⟩
    exact (mem_windowEvent_iff ha σ).mpr hs
  · rintro ⟨a, ha⟩
    have hav : a.val + m ≤ N := by have := a.isLt; omega
    refine ⟨a.val, hav, ?_⟩
    exact (mem_windowEvent_iff hav σ).mp ha

/-- U06: the uniform increasing-run probability has the exact number of starts in its bound. -/
theorem prob_increasingRun_le {N m : ℕ} (hm : m ≤ N) :
    prob (uniformLaw (Equiv.Perm (Fin N)))
      (univ.filter (fun σ => HasIncreasingRun σ m)) ≤
        ((N - m + 1 : ℕ) : ℝ) / (m.factorial : ℝ) := by
  classical
  rw [increasingRun_eq_union hm]
  calc
    prob (uniformLaw (Equiv.Perm (Fin N)))
        (unionEvents (fun a : Fin (N - m + 1) =>
          windowEvent N m a.val (by have := a.isLt; omega)) univ) ≤
        ∑ a : Fin (N - m + 1), prob (uniformLaw (Equiv.Perm (Fin N)))
          (windowEvent N m a.val (by have := a.isLt; omega)) :=
      prob_unionEvents_le _ _ _
    _ = ∑ _a : Fin (N - m + 1), 1 / (m.factorial : ℝ) := by
      apply sum_congr rfl
      intro a _
      exact prob_increasingAlong _
    _ = ((N - m + 1 : ℕ) : ℝ) / (m.factorial : ℝ) := by
      simp [div_eq_mul_inv]

/-- U07: either ordering of two distinct positions occurs with probability one half. -/
theorem prob_ascent {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    prob (uniformLaw (Equiv.Perm (Fin N))) (ascentEvent i j) = 1 / 2 := by
  classical
  let e : Fin 2 ↪ Fin N :=
    { toFun := fun a => if a = 0 then i else j
      inj' := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all }
  have he : ascentEvent i j = increasingAlongEvent e := by
    ext σ
    simp only [ascentEvent, increasingAlongEvent, mem_filter, mem_univ, true_and,
      increasingAlong]
    constructor
    · intro h a b hab
      fin_cases a <;> fin_cases b <;> simp_all [e]
    · intro h
      have hv := h (show (0 : Fin 2) < 1 by decide)
      simpa [e] using hv
  rw [he]
  simpa [Nat.factorial] using prob_increasingAlong e

/-- U08: the exact uniform ascent mean uses linearity, not independence. -/
theorem expect_ascentCount {N : ℕ} (E : Finset (Fin N × Fin N))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) :
    expect (uniformLaw (Equiv.Perm (Fin N))) (ascentCount E) = (E.card : ℝ) / 2 := by
  classical
  change expect (uniformLaw (Equiv.Perm (Fin N)))
    (fun σ => ∑ e ∈ E, if σ e.1 < σ e.2 then 1 else 0) = _
  rw [expect_sum]
  calc
    ∑ e ∈ E, expect (uniformLaw (Equiv.Perm (Fin N)))
        (fun σ => if σ e.1 < σ e.2 then 1 else 0) =
        ∑ _e ∈ E, (1 / 2 : ℝ) := by
      apply sum_congr rfl
      intro e he
      have hi := expect_indicator (uniformLaw (Equiv.Perm (Fin N))) (ascentEvent e.1 e.2)
      simp only [ascentEvent, mem_filter, mem_univ, true_and] at hi
      exact hi.trans (prob_ascent e.1 e.2 (hE e he))
    _ = (E.card : ℝ) / 2 := by simp [div_eq_mul_inv]

end RiffleLower
