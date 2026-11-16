import RiffleLowerV2.Types.Rounding
import Mathlib.Data.Fintype.Perm

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Types
open TimeProfile
attribute [local instance 2000] Classical.propDecidable

private def fiberEquiv {J S A : Type*} (f : J → A) (g : S → A)
    (e : J ≃ S) (he : ∀ j, g (e j) = f j) (a : A) :
    {j // f j = a} ≃ {s // g s = a} where
  toFun j := ⟨e j.val, (he j.val).trans j.property⟩
  invFun s := ⟨e.symm s.val, by rw [← he, e.apply_symm_apply]; exact s.property⟩
  left_inv j := Subtype.ext (e.symm_apply_apply j.val)
  right_inv s := Subtype.ext (e.apply_symm_apply s.val)

private def equivFiberwise {J S A : Type*} (f : J → A) (g : S → A) :
    {e : J ≃ S // ∀ j, g (e j) = f j} ≃
      (∀ a, {j // f j = a} ≃ {s // g s = a}) where
  toFun e a := fiberEquiv f g e.val e.property a
  invFun e := ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩
  left_inv e := by apply Subtype.ext; ext j; rfl
  right_inv e := by
    funext a
    apply Equiv.ext
    rintro ⟨j, hj⟩
    subst a
    rfl

private def sigmaFirstFiber {A : Type*} (c : A → ℕ) (a : A) :
    {s : (Σ b, Fin (c b)) // s.fst = a} ≃ Fin (c a) where
  toFun s := s.property ▸ s.val.snd
  invFun x := ⟨⟨a, x⟩, rfl⟩
  left_inv := by rintro ⟨⟨b, x⟩, h⟩; subst a; rfl
  right_inv _ := rfl

/-- Words with a prescribed multiplicity of every letter, on any finite domain. -/
def prescribedWords (J A : Type*) [Fintype J] [Fintype A] (c : A → ℕ) :
    Finset (J → A) :=
  Finset.univ.filter fun f => ∀ a, Fintype.card {j // f j = a} = c a

private theorem mem_prescribedWords {J A : Type*} [Fintype J] [Fintype A]
    (c : A → ℕ) (f : J → A) :
    f ∈ prescribedWords J A c ↔ ∀ a, Fintype.card {j // f j = a} = c a := by
  simp [prescribedWords]

private def wordOfEquiv {J A : Type*} [Fintype J] [Fintype A]
    (c : A → ℕ) (e : J ≃ (Σ a, Fin (c a))) : prescribedWords J A c := by
  classical
  refine ⟨fun j => (e j).fst, (mem_prescribedWords c _).mpr ?_⟩
  intro a
  have h := Fintype.card_congr
    ((fiberEquiv (fun j => (e j).fst) Sigma.fst e (fun _ => rfl) a).trans
      (sigmaFirstFiber c a))
  simpa using h

theorem prescribedWords_nonempty {J A : Type*} [Fintype J] [Fintype A]
    (c : A → ℕ) (htotal : ∑ a, c a = Fintype.card J) :
    (prescribedWords J A c).Nonempty := by
  classical
  have hcard : Fintype.card J = Fintype.card (Σ a, Fin (c a)) := by
    simpa using htotal.symm
  exact ⟨(wordOfEquiv c (Fintype.equivOfCardEq hcard)).val,
    (wordOfEquiv c (Fintype.equivOfCardEq hcard)).property⟩

private def wordEquivFiber {J A : Type*} [Fintype J] [Fintype A]
    (c : A → ℕ) (w : prescribedWords J A c) :
    {e : J ≃ (Σ a, Fin (c a)) // wordOfEquiv c e = w} ≃
      {e : J ≃ (Σ a, Fin (c a)) // ∀ j, (e j).fst = w.val j} :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun e => by
    constructor
    · intro h j
      exact congrArg (fun v : prescribedWords J A c => v.val j) h
    · intro h
      apply Subtype.ext
      funext j
      exact h j)

/-- A finite fiber count; the denominator is an exact divisor. -/
theorem prescribedWords_card_mul {J A : Type*} [Fintype J] [Fintype A]
    (c : A → ℕ) (htotal : ∑ a, c a = Fintype.card J) :
    (prescribedWords J A c).card * (∏ a, (c a).factorial) =
      (Fintype.card J).factorial := by
  classical
  have hcard : Fintype.card J = Fintype.card (Σ a, Fin (c a)) := by
    simpa using htotal.symm
  have hfiber (w : prescribedWords J A c) :
      Fintype.card {e : J ≃ (Σ a, Fin (c a)) // wordOfEquiv c e = w} =
        ∏ a, (c a).factorial := by
    rw [Fintype.card_congr (wordEquivFiber c w)]
    have hw := (mem_prescribedWords c w.val).mp w.property
    have hmatch (a : A) : Fintype.card {j // w.val j = a} =
        Fintype.card {s : (Σ a, Fin (c a)) // s.fst = a} := by
      rw [hw a, Fintype.card_congr (sigmaFirstFiber c a), Fintype.card_fin]
    calc
      _ = Fintype.card (∀ a, {j // w.val j = a} ≃
          {s : (Σ a, Fin (c a)) // s.fst = a}) :=
        Fintype.card_congr (equivFiberwise w.val Sigma.fst)
      _ = ∏ a, (c a).factorial := by
        rw [Fintype.card_pi]
        apply Finset.prod_congr rfl
        intro a _
        calc
          _ = (Fintype.card {j // w.val j = a}).factorial :=
            Fintype.card_equiv (Fintype.equivOfCardEq (hmatch a))
          _ = (c a).factorial := by rw [hw a]
  calc
    (prescribedWords J A c).card * (∏ a, (c a).factorial) =
        ∑ w : prescribedWords J A c,
          Fintype.card {e : J ≃ (Σ a, Fin (c a)) // wordOfEquiv c e = w} := by
      simp_rw [hfiber]
      simp
    _ = Fintype.card (Σ w : prescribedWords J A c,
          {e : J ≃ (Σ a, Fin (c a)) // wordOfEquiv c e = w}) := by
      rw [Fintype.card_sigma]
    _ = Fintype.card (J ≃ (Σ a, Fin (c a))) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv (wordOfEquiv (J := J) c))
    _ = (Fintype.card J).factorial :=
      Fintype.card_equiv (Fintype.equivOfCardEq hcard)

/-- Exact multinomial count on an arbitrary finite position set. -/
theorem prescribedWords_card {J A : Type*} [Fintype J] [Fintype A]
    (c : A → ℕ) (htotal : ∑ a, c a = Fintype.card J) :
    (prescribedWords J A c).card =
      (Fintype.card J).factorial / ∏ a, (c a).factorial := by
  rw [← prescribedWords_card_mul c htotal]
  have hp : 0 < ∏ a, (c a).factorial :=
    Finset.prod_pos (fun a _ => Nat.factorial_pos (c a))
  exact (Nat.mul_div_cancel _ hp).symm

/-- Exact cell-by-cell multiplicities on a finite domain. -/
def prescribedCellWords {J A B : Type*} [Fintype J] [Fintype A] [Fintype B]
    (cell : J → A) (c : A → B → ℕ) : Finset (J → B) :=
  Finset.univ.filter fun f =>
    ∀ a b, Fintype.card {j // cell j = a ∧ f j = b} = c a b

private theorem mem_prescribedCellWords {J A B : Type*}
    [Fintype J] [Fintype A] [Fintype B] (cell : J → A) (c : A → B → ℕ)
    (f : J → B) : f ∈ prescribedCellWords cell c ↔
      ∀ a b, Fintype.card {j // cell j = a ∧ f j = b} = c a b := by
  simp [prescribedCellWords]

private def cellAssemble {J A B : Type*} (cell : J → A)
    (f : ∀ a, {j // cell j = a} → B) (j : J) : B := f (cell j) ⟨j, rfl⟩

private theorem cellAssemble_apply {J A B : Type*} (cell : J → A)
    (f : ∀ a, {j // cell j = a} → B) (j : J) (a : A) (h : cell j = a) :
    cellAssemble cell f j = f a ⟨j, h⟩ := by
  subst a
  rfl

private def prescribedCellWordsEquiv {J A B : Type*}
    [Fintype J] [Fintype A] [Fintype B] (cell : J → A) (c : A → B → ℕ) :
    prescribedCellWords cell c ≃
      (∀ a, prescribedWords {j // cell j = a} B (c a)) where
  toFun w a := ⟨fun j => w.val j.val, (mem_prescribedWords (c a) _).mpr (by
    intro b
    calc
      _ = Fintype.card {j // cell j = a ∧ w.val j = b} :=
        Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun j => cell j = a) (fun j => w.val j = b))
      _ = c a b := (mem_prescribedCellWords cell c w.val).mp w.property a b)⟩
  invFun w := ⟨cellAssemble cell (fun a => (w a).val),
    (mem_prescribedCellWords cell c _).mpr (by
      intro a b
      have hrestrict : (fun j : {j // cell j = a} =>
          cellAssemble cell (fun a => (w a).val) j.val) = (w a).val := by
        funext j
        exact cellAssemble_apply cell _ j.val a j.property
      calc
        _ = Fintype.card {j : {j // cell j = a} //
            cellAssemble cell (fun a => (w a).val) j.val = b} :=
          Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun j => cell j = a)
            (fun j => cellAssemble cell (fun a => (w a).val) j = b)).symm
        _ = Fintype.card {j // (w a).val j = b} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun j => by
            rw [congrFun hrestrict j]))
        _ = c a b := (mem_prescribedWords (c a) (w a).val).mp (w a).property b)⟩
  left_inv w := by apply Subtype.ext; rfl
  right_inv w := by
    funext a
    apply Subtype.ext
    funext j
    exact cellAssemble_apply cell (fun a => (w a).val) j.val a j.property

theorem prescribedCellWords_nonempty {J A B : Type*}
    [Fintype J] [Fintype A] [Fintype B] (cell : J → A) (c : A → B → ℕ)
    (htotal : ∀ a, ∑ b, c a b = Fintype.card {j // cell j = a}) :
    (prescribedCellWords cell c).Nonempty := by
  classical
  have hw (a : A) := prescribedWords_nonempty (c a) (htotal a)
  let w : ∀ a, prescribedWords {j // cell j = a} B (c a) :=
    fun a => ⟨(hw a).choose, (hw a).choose_spec⟩
  exact ⟨((prescribedCellWordsEquiv cell c).symm w).val,
    ((prescribedCellWordsEquiv cell c).symm w).property⟩

theorem prescribedCellWords_card {J A B : Type*}
    [Fintype J] [Fintype A] [Fintype B] (cell : J → A) (c : A → B → ℕ)
    (htotal : ∀ a, ∑ b, c a b = Fintype.card {j // cell j = a}) :
    (prescribedCellWords cell c).card =
      ∏ a, (Fintype.card {j // cell j = a}).factorial / ∏ b, (c a b).factorial := by
  classical
  calc
    _ = Fintype.card (prescribedCellWords cell c) := (Fintype.card_coe _).symm
    _ = Fintype.card (∀ a, prescribedWords {j // cell j = a} B (c a)) :=
      Fintype.card_congr (prescribedCellWordsEquiv cell c)
    _ = ∏ a, (prescribedWords {j // cell j = a} B (c a)).card := by
      rw [Fintype.card_pi]
      simp
    _ = _ := Finset.prod_congr rfl (fun a _ => prescribedWords_card (c a) (htotal a))

private def finiteSetFiberEquiv {J : Type*} (I : Finset J) (p : J → Prop) :
    {j : I // p j.val} ≃ (I.filter p) where
  toFun j := ⟨j.val.val, Finset.mem_filter.mpr ⟨j.val.property, j.property⟩⟩
  invFun j := ⟨⟨j.val, (Finset.mem_filter.mp j.property).1⟩,
    (Finset.mem_filter.mp j.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cellPositionCount_eq_fiberCard {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (P : BorelPartition k) (I : Finset (Fin K))
    (i : Fin P.cellCount) :
    cellPositionCount cuts hN P I i =
      Fintype.card {j : I // P.classify (cuts.profile hN j.val) = i} := by
  symm
  calc
    _ = Fintype.card (I.filter fun j => P.classify (cuts.profile hN j) = i) :=
      Fintype.card_congr (finiteSetFiberEquiv I
        (fun j => P.classify (cuts.profile hN j) = i))
    _ = (I.filter fun j => P.classify (cuts.profile hN j) = i).card :=
      Fintype.card_coe _
    _ = _ := by unfold cellPositionCount; congr 2

theorem wordCellCount_eq_fiberCard {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (P : BorelPartition k) {I : Finset (Fin K)} (x : WordOn k I)
    (i : Fin P.cellCount) (l : Fin k) :
    wordCellCount cuts hN P x i l =
      Fintype.card {j : I // P.classify (cuts.profile hN j.val) = i ∧ x j = l} := by
  rw [Fintype.card_subtype]
  unfold wordCellCount
  congr 2

theorem roundedClass_eq_prescribedCellWords {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (P : BorelPartition k) (I : Finset (Fin K))
    (D : RoundedTypeData P) :
    roundedClass cuts hN P I D =
      prescribedCellWords (fun j : I => P.classify (cuts.profile hN j.val)) D.count := by
  have hdef : roundedClass cuts hN P I D =
      Finset.univ.filter (fun x : WordOn k I =>
        ∀ i l, wordCellCount cuts hN P x i l = D.count i l) := by
    unfold roundedClass
    congr 2
    exact Subsingleton.elim _ _
  rw [hdef]
  ext x
  constructor
  · intro hx
    have h := (Finset.mem_filter.mp hx).2
    apply (mem_prescribedCellWords _ _ x).mpr
    intro i l
    rw [← wordCellCount_eq_fiberCard]
    exact h i l
  · intro hx
    have h := (mem_prescribedCellWords _ _ x).mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i l
    rw [wordCellCount_eq_fiberCard]
    exact h i l

/-- Compatible exact totals produce a nonempty rounded class, including empty cells. -/
theorem roundedClass_nonempty {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (P : BorelPartition k) (I : Finset (Fin K))
    (D : RoundedTypeData P)
    (htotal : ∀ i, ∑ l, D.count i l = cellPositionCount cuts hN P I i) :
    (roundedClass cuts hN P I D).Nonempty := by
  rw [roundedClass_eq_prescribedCellWords]
  apply prescribedCellWords_nonempty
  intro i
  rw [← cellPositionCount_eq_fiberCard]
  exact htotal i

/-- Exact product of natural factorial quotients for the frozen rounded class. -/
theorem roundedClass_card {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (P : BorelPartition k) (I : Finset (Fin K))
    (D : RoundedTypeData P)
    (htotal : ∀ i, ∑ l, D.count i l = cellPositionCount cuts hN P I i) :
    (roundedClass cuts hN P I D).card =
      ∏ i : Fin P.cellCount, (cellPositionCount cuts hN P I i).factorial /
        ∏ l : Fin k, (D.count i l).factorial := by
  have htotal' (i : Fin P.cellCount) : ∑ l, D.count i l =
      Fintype.card {j : I // P.classify (cuts.profile hN j.val) = i} := by
    rw [← cellPositionCount_eq_fiberCard]
    exact htotal i
  rw [roundedClass_eq_prescribedCellWords, prescribedCellWords_card _ _ htotal']
  apply Finset.prod_congr rfl
  intro i _
  rw [← cellPositionCount_eq_fiberCard]

end RiffleLowerV2.Types
