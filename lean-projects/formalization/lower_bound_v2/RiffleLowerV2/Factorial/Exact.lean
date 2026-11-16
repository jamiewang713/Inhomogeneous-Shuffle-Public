import RiffleLowerV2.Factorial.Basic
import RiffleLowerV2.Factorial.Requests

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
set_option maxHeartbeats 400000

namespace RiffleLowerV2.Factorial
open TimeProfile

def requestColumnEquiv {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (σ : Equiv.Perm (Fin N)) : ColumnAssignments cuts j ≃ ColumnAssignments cuts j where
  toFun a := ⟨fun i => a.val (σ i), by
    intro l
    have he : (Finset.univ.filter fun i => a.val (σ i) = l).card =
        (Finset.univ.filter fun i => a.val i = l).card := by
      apply Finset.card_bij (fun i _ => σ i)
      · intro i hi; simpa using hi
      · intro i _ m _ him; exact σ.injective him
      · intro i hi; exact ⟨σ.symm i, by simpa using hi, by simp⟩
    exact he.trans (a.property l)⟩
  invFun a := ⟨fun i => a.val (σ.symm i), by
    intro l
    have he : (Finset.univ.filter fun i => a.val (σ.symm i) = l).card =
        (Finset.univ.filter fun i => a.val i = l).card := by
      apply Finset.card_bij (fun i _ => σ.symm i)
      · intro i hi; simpa using hi
      · intro i _ m _ him; exact σ.symm.injective him
      · intro i hi; exact ⟨σ i, by simpa using hi, by simp⟩
    exact he.trans (a.property l)⟩
  left_inv a := by apply Subtype.ext; funext i; simp
  right_inv a := by apply Subtype.ext; funext i; simp

@[simp] theorem requestColumnEquiv_apply {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (σ : Equiv.Perm (Fin N)) (a : ColumnAssignments cuts j) (i : Fin N) :
    (requestColumnEquiv cuts j σ a).val i = a.val (σ i) := rfl

theorem column_request_probability {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    {A : Type*} [Fintype A] (f : A → Fin k) (e : A ↪ Fin N) :
    expect (columnPMF cuts j) (fun a => if ∀ x, a.val (e x) = f x then 1 else 0) =
      (∏ a, falling (cuts.count j a) (Nat.card {x // f x = a})) /
        falling N (Fintype.card A) := by
  classical
  let q : (A ↪ Fin N) → ℝ := fun e =>
    expect (columnPMF cuts j) (fun a => if ∀ x, a.val (e x) = f x then 1 else 0)
  have hq (e' : A ↪ Fin N) : q e' = q e := by
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair e e' e.injective e'.injective
    have h := uniform_expect_equiv (requestColumnEquiv cuts j σ)
      (fun a => if ∀ x, a.val (e x) = f x then (1 : ℝ) else 0)
    simpa only [requestColumnEquiv_apply, hσ, q, columnPMF] using h
  have hpoint (a : ColumnAssignments cuts j) :
      (∑ e' : A ↪ Fin N, if ∀ x, a.val (e' x) = f x then (1 : ℝ) else 0) =
        ∏ l, falling (cuts.count j l) (Nat.card {x // f x = l}) := by
    have h := coloredEmbeddings_natCard f a.val
    have hc (l : Fin k) : Nat.card {y // a.val y = l} = cuts.count j l := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact a.property l
    have h' : Nat.card (ColoredEmbeddings f a.val) =
        ∏ l, (cuts.count j l).descFactorial (Nat.card {x // f x = l}) :=
      h.trans (Finset.prod_congr rfl fun l _ =>
        congrArg (fun n => n.descFactorial (Nat.card {x // f x = l})) (hc l))
    have hh := congrArg (fun n : ℕ => (n : ℝ)) h'
    simpa only [ColoredEmbeddings, falling, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_prod,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hh
  have hs : falling N (Fintype.card A) * q e =
      ∏ l, falling (cuts.count j l) (Nat.card {x // f x = l}) := by
    calc
      falling N (Fintype.card A) * q e = ∑ e' : A ↪ Fin N, q e' := by
        simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_embedding_eq, Fintype.card_fin, falling]
      _ = expect (columnPMF cuts j) (fun a =>
          ∑ e' : A ↪ Fin N, if ∀ x, a.val (e' x) = f x then 1 else 0) :=
        (expect_sum _ Finset.univ _).symm
      _ = _ := by simp only [hpoint, expect_const]
  have hpos : 0 < falling N (Fintype.card A) := by
    unfold falling
    exact_mod_cast (Nat.descFactorial_pos.mpr
      (by simpa using Fintype.card_le_of_embedding e))
  exact (eq_div_iff (ne_of_gt hpos)).2 (by simpa only [mul_comm] using hs)

theorem request_column_product {k N K : ℕ} (cuts : Cuts k N K)
    (f : ∀ j, ColumnAssignments cuts j → ℝ) :
    expect (fixedCountPMF cuts) (fun ω => ∏ j, f j (ω j)) =
      ∏ j, expect (columnPMF cuts j) (f j) := by
  rw [fixed_expect_eq_average]
  simp_rw [columnPMF, uniform_expect]
  simp only [Sample, ShuffleSample]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Fintype.card_pi, Nat.cast_prod]

theorem request_probability {k N K d : ℕ} (cuts : Cuts k N K)
    (w : Fin d → Word k K) (r : Fin d → ℕ) (e : (Σ i, Fin (r i)) ↪ Fin N) :
    expect (fixedCountPMF cuts)
      (fun ω => if ∀ x, rowWord ω (e x) = w x.1 then 1 else 0) =
      ∏ j, ((∏ a, falling (cuts.count j a) (requestedCount w r j a)) /
        falling N (∑ i, r i)) := by
  classical
  let f : ∀ j, ColumnAssignments cuts j → ℝ := fun j a =>
    if ∀ x : Σ i, Fin (r i), a.val (e x) = (w x.1).get j then 1 else 0
  have hp (ω : Sample cuts) :
      (if ∀ x, rowWord ω (e x) = w x.1 then (1 : ℝ) else 0) = ∏ j, f j (ω j) := by
    have he : (∀ x, rowWord ω (e x) = w x.1) ↔
        ∀ j, ∀ x, (ω j).val (e x) = (w x.1).get j := by
      constructor
      · intro h j x
        have hh := congrArg (fun v : Word k K => v.get j) (h x)
        simpa only [rowWord_get, sampleEntry] using hh
      · intro h x
        apply List.Vector.ext
        intro j
        simpa only [rowWord_get, sampleEntry] using h j x
    by_cases h : ∀ j, ∀ x, (ω j).val (e x) = (w x.1).get j
    · simp [he, h, f]
    · rw [if_neg (fun h' => h (he.mp h'))]
      push Not at h
      obtain ⟨j, x, hx⟩ := h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (fun hh => hx (hh x)))
  have hfun := funext hp
  rw [hfun, request_column_product]
  apply Finset.prod_congr rfl
  intro j _
  change expect (columnPMF cuts j)
    (fun a => if ∀ x : Σ i, Fin (r i), a.val (e x) = (w x.1).get j then 1 else 0) = _
  rw [column_request_probability]
  congr 1
  · apply Finset.prod_congr rfl
    intro a _
    apply congrArg (falling (cuts.count j a))
    rw [Nat.card_eq_fintype_card]
    exact (requestedCount_eq_card w r j a).symm
  · congr 1
    simp only [Fintype.card_sigma, Fintype.card_fin]

theorem exactJointFactorial : Targets.ExactJointFactorial := by
  intro k N K d cuts w r hw _hR
  have hfun : factorialProduct (cuts := cuts) w r = fun ω =>
      ∑ e : (Σ i, Fin (r i)) ↪ Fin N,
        if ∀ x, rowWord ω (e x) = w x.1 then (1 : ℝ) else 0 :=
    funext (factorialProduct_eq_requests w r hw)
  rw [hfun]
  rw [expect_sum]
  simp_rw [request_probability]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_sigma, exactFactorial,
    falling]

end RiffleLowerV2.Factorial
