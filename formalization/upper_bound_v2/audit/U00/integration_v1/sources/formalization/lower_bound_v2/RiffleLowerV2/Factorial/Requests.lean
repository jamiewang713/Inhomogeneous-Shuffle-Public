import Contracts.v1.FactorialOccupancy
import RiffleLowerV2.Shared.Adapters
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
set_option maxHeartbeats 400000

namespace RiffleLowerV2.Factorial
open TimeProfile

abbrev ColoredEmbeddings {A B C : Type*} (f : A → C) (g : B → C) :=
  {e : A ↪ B // ∀ x, g (e x) = f x}

def coloredEmbeddingsEquiv {A B C : Type*} (f : A → C) (g : B → C) :
    ColoredEmbeddings f g ≃ (∀ c, {x // f x = c} ↪ {y // g y = c}) where
  toFun e c :=
    ⟨fun x => ⟨e.val x.val, (e.property x.val).trans x.property⟩,
      fun x y h => Subtype.ext (e.val.injective (congrArg Subtype.val h))⟩
  invFun h := ⟨⟨fun x => (h (f x) ⟨x, rfl⟩).val, by
    intro x y he
    dsimp only at he
    have hc : f x = f y := by
      have hx := (h (f x) ⟨x, rfl⟩).property
      have hy := (h (f y) ⟨y, rfl⟩).property
      rw [he] at hx
      exact hx.symm.trans hy
    have hy : (h (f y) ⟨y, rfl⟩).val = (h (f x) ⟨y, hc.symm⟩).val := by
      have hv (c c' : C) (hh : c = c') (u : {x // f x = c})
          (v : {x // f x = c'}) (huv : u.val = v.val) :
          (h c u).val = (h c' v).val := by
        subst c'
        have huv' : u = v := Subtype.ext huv
        rw [huv']
      exact hv _ _ hc.symm _ _ rfl
    rw [hy] at he
    exact congrArg Subtype.val ((h (f x)).injective (Subtype.ext he))⟩,
    fun x => (h (f x) ⟨x, rfl⟩).property⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro x
    rfl
  right_inv h := by
    funext c
    apply Function.Embedding.ext
    intro x
    apply Subtype.ext
    rcases x with ⟨x, hx⟩
    cases hx
    rfl

theorem coloredEmbeddings_card {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → C) (g : B → C) :
    Fintype.card (ColoredEmbeddings f g) =
      ∏ c, (Fintype.card {y // g y = c}).descFactorial
        (Fintype.card {x // f x = c}) := by
  classical
  rw [Fintype.card_congr (coloredEmbeddingsEquiv f g), Fintype.card_pi]
  simp only [Fintype.card_embedding_eq]

theorem coloredEmbeddings_natCard {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → C) (g : B → C) :
    Nat.card (ColoredEmbeddings f g) =
      ∏ c, (Nat.card {y // g y = c}).descFactorial (Nat.card {x // f x = c}) := by
  simpa only [Nat.card_eq_fintype_card] using coloredEmbeddings_card f g

def groupedEmbeddingsEquiv {I B C : Type*} (r : I → ℕ) (w : I → C)
    (hw : Function.Injective w) (g : B → C) :
    (∀ i, Fin (r i) ↪ {y // g y = w i}) ≃
      ColoredEmbeddings (fun x : Σ i, Fin (r i) => w x.1) g where
  toFun h := ⟨⟨fun x => (h x.1 x.2).val, by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    dsimp only at he
    have hij : i = j := hw (by
      have hi := (h i x).property
      have hj := (h j y).property
      rw [he] at hi
      exact hi.symm.trans hj)
    subst j
    have hxy := (h i).injective (Subtype.ext he)
    exact congrArg (Sigma.mk i) hxy⟩, fun x => (h x.1 x.2).property⟩
  invFun e i := ⟨fun x => ⟨e.val ⟨i, x⟩, e.property ⟨i, x⟩⟩, by
    intro x y he
    have hs := e.val.injective (congrArg Subtype.val he)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2⟩
  left_inv h := by
    funext i
    apply Function.Embedding.ext
    intro x
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    rintro ⟨i, x⟩
    rfl

theorem wordCount_eq_card {k N K : ℕ} {cuts : Cuts k N K}
    (w : Word k K) (ω : Sample cuts) :
    wordCount w ω = Fintype.card {i : Fin N // rowWord ω i = w} := by
  classical
  change (Finset.univ.filter fun i => (rowWord ω i).toList.take K = w.toList).card = _
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp +instances only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.take_of_length_le (by simp)]
  exact List.Vector.toList_injective.eq_iff

theorem factorialProduct_eq_requests {k N K d : ℕ} {cuts : Cuts k N K}
    (w : Fin d → Word k K) (r : Fin d → ℕ) (hw : Function.Injective w)
    (ω : Sample cuts) :
    factorialProduct w r ω =
      ∑ e : (Σ i, Fin (r i)) ↪ Fin N,
        if ∀ x, rowWord ω (e x) = w x.1 then 1 else 0 := by
  classical
  have hc := Fintype.card_congr (groupedEmbeddingsEquiv r w hw (rowWord ω))
  rw [Fintype.card_pi] at hc
  simp only [Fintype.card_embedding_eq, Fintype.card_fin] at hc
  unfold factorialProduct
  simp only [falling, wordCount_eq_card, ← Nat.cast_prod]
  rw [hc]
  change (Fintype.card {e : (Σ i, Fin (r i)) ↪ Fin N //
      ∀ x, rowWord ω (e x) = w x.1} : ℝ) = _
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, apply_ite, Nat.cast_one, Nat.cast_zero]

theorem requestedCount_eq_card {k K d : ℕ} (w : Fin d → Word k K)
    (r : Fin d → ℕ) (j : Fin K) (a : Fin k) :
    requestedCount w r j a =
      Fintype.card {x : Σ i, Fin (r i) // (w x.1).get j = a} := by
  classical
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_sigma]
  unfold requestedCount
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (w i).get j = a <;> simp [h]

end RiffleLowerV2.Factorial
