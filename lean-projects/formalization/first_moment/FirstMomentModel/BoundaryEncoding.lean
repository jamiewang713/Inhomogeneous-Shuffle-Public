import Riffle.Boundary
import FirstMoment.Counting
import Mathlib.Data.Finite.Card

/-!
Actual admissible-boundary encodings from the frozen supplemental contract.
The code keeps terminal first crossings distinct from terminal fallbacks.
-/

namespace InhomogeneousShuffle.FirstMoment.Model

noncomputable section

variable {D : Riffle.Model}

def boundaryBudget (A : Riffle.Setup D) : ℕ :=
  Nat.floor (A.C / Real.log (1 / A.chi) * Real.log (D.N : ℝ))

def outward (A : Riffle.Setup D) (s : Riffle.Side) (x : Riffle.Word) (i : ℕ) : Prop :=
  match s with
  | .left => Riffle.digit x i < Riffle.leftIndex A i
  | .right => Riffle.rightIndex A i < Riffle.digit x i

def boundaryPositions (A : Riffle.Setup D) (s : Riffle.Side)
    (x : Riffle.Word) : Finset (Fin D.K) := by
  classical
  exact Finset.univ.filter (fun i =>
    A.w.length ≤ i.val ∧ i.val < x.length ∧ outward A s x i.val)

theorem boundaryPositions_card (A : Riffle.Setup D) (s : Riffle.Side)
    (x : Riffle.Word) (hx : x.length ≤ D.K) :
    (boundaryPositions A s x).card = Riffle.violations A s x := by
  classical
  unfold boundaryPositions Riffle.violations
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, ?_⟩
    cases s <;> exact h.2.2
  · intro i hi j hj h
    exact Fin.ext h
  · intro i hi
    have h := Finset.mem_filter.mp hi
    have hb := Finset.mem_Ico.mp h.1
    refine ⟨⟨i, hb.2.trans_le hx⟩, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.1, hb.2, ?_⟩
    cases s <;> exact h.2

theorem admissible_violations_le_budget (A : Riffle.Setup D)
    (s : Riffle.Side) {x : Riffle.Word} (hx : x ∈ Riffle.Admissible A s) :
    Riffle.violations A s x ≤ boundaryBudget A :=
  Nat.le_floor hx.2

def boundaryTag (A : Riffle.Setup D) (s : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A s}) : Fin (D.k + 1) := by
  classical
  exact if h : A.w.length < x.val.length ∧
      Riffle.Cross A s x.val (x.val.length - 1) then
    ⟨Riffle.digit x.val (x.val.length - 1),
      lt_trans (x.property.1.1.1.2 _ (by omega)).1 (Nat.lt_succ_self D.k)⟩
  else Fin.last D.k

def encodeBoundary (A : Riffle.Setup D) (s : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A s}) :
    BoundaryCode D.K D.k (boundaryBudget A) := by
  classical
  have hx : Riffle.Legal D x.val := x.property.1.1.1
  refine ⟨⟨x.val.length, Nat.lt_succ_of_le hx.1⟩, boundaryTag A s x, ?_⟩
  refine ⟨⟨boundaryPositions A s x.val, ?_⟩, ?_⟩
  · rw [boundaryPositions_card A s x.val hx.1]
    exact admissible_violations_le_budget A s x.property
  · intro i
    have hi : i.val.val < x.val.length := (Finset.mem_filter.mp i.property).2.2.1
    exact ⟨Riffle.digit x.val i.val.val, (hx.2 _ hi).1⟩

def decodeBoundary (A : Riffle.Setup D) (s : Riffle.Side)
    (c : BoundaryCode D.K D.k (boundaryBudget A)) : Riffle.Word := by
  classical
  exact List.ofFn (fun i : Fin c.1.val =>
    if i.val < A.w.length then Riffle.digit A.w i.val
    else
      let j : Fin D.K := ⟨i.val, i.isLt.trans_le (Nat.le_of_lt_succ c.1.isLt)⟩
      if hj : j ∈ c.2.2.1.val then (c.2.2.2 ⟨j, hj⟩).val
      else if i.val + 1 = c.1.val ∧ c.2.1.val < D.k then c.2.1.val
      else match s with
        | .left => Riffle.leftIndex A i.val
        | .right => Riffle.rightIndex A i.val)

theorem decode_encode_boundary (A : Riffle.Setup D) (s : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A s}) :
    decodeBoundary A s (encodeBoundary A s x) = x.val := by
  classical
  have hx : Riffle.Legal D x.val := x.property.1.1.1
  have hpre : A.w <+: x.val := x.property.1.1.2
  have hb : x.val ∈ Riffle.Boundary A s := x.property.1
  apply List.ext_getElem
  · simp [decodeBoundary, encodeBoundary]
  · intro i hi hj
    have hiK : i < D.K := hj.trans_le hx.1
    by_cases hiw : i < A.w.length
    · have he : Riffle.digit A.w i = Riffle.digit x.val i := Riffle.digit_prefix hpre hiw
      simpa [decodeBoundary, encodeBoundary, hiw, Riffle.digit, hj] using he
    · have hwi : A.w.length ≤ i := Nat.le_of_not_gt hiw
      by_cases hout : outward A s x.val i
      · simp [decodeBoundary, encodeBoundary, hiw, boundaryPositions, hwi, hj,
          hout, Riffle.digit]
      · rcases hb.2 with hcross | hfallback
        · have hflag : A.w.length < x.val.length ∧
              Riffle.Cross A s x.val (x.val.length - 1) := ⟨hcross.1, hcross.2.1⟩
          have hlast : x.val.length - 1 < x.val.length := by omega
          have htag : (boundaryTag A s x).val = Riffle.digit x.val (x.val.length - 1) := by
            simp [boundaryTag, hflag]
          have htaglt : (boundaryTag A s x).val < D.k := by
            rw [htag]
            exact (hx.2 _ hlast).1
          by_cases hilast : i + 1 = x.val.length
          · have hei : x.val.length - 1 = i := by omega
            have hdi : x.val[i] < D.k := by
              simpa [Riffle.digit, hj] using (hx.2 i hj).1
            simp [decodeBoundary, encodeBoundary, hiw, boundaryPositions, hwi, hj,
              hout, hilast, htaglt, htag, hei, Riffle.digit, hdi]
          · have hnotcross := hcross.2.2 i hwi (show i < x.val.length - 1 by omega)
            have he : (match s with
                | .left => Riffle.leftIndex A i
                | .right => Riffle.rightIndex A i) = Riffle.digit x.val i := by
              cases s <;> simp only [outward, Riffle.Cross, Riffle.crossDigit] at hout hnotcross ⊢ <;>
                omega
            cases s <;>
              simpa [decodeBoundary, encodeBoundary, hiw, boundaryPositions, hwi, hj,
                hout, hilast, Riffle.digit] using he
        · have hflag : ¬(A.w.length < x.val.length ∧
              Riffle.Cross A s x.val (x.val.length - 1)) := by
            intro h
            exact hfallback.2 (x.val.length - 1) (by omega) (by omega) h.2
          have htag : (boundaryTag A s x).val = D.k := by simp [boundaryTag, hflag]
          have hnotcross := hfallback.2 i hwi (by omega)
          have he : (match s with
              | .left => Riffle.leftIndex A i
              | .right => Riffle.rightIndex A i) = Riffle.digit x.val i := by
            cases s <;> simp only [outward, Riffle.Cross, Riffle.crossDigit] at hout hnotcross ⊢ <;>
              omega
          cases s <;>
            simpa [decodeBoundary, encodeBoundary, hiw, boundaryPositions, hwi, hj,
              hout, htag, Riffle.digit] using he

theorem encodeBoundary_injective (A : Riffle.Setup D) (s : Riffle.Side) :
    Function.Injective (encodeBoundary A s) := by
  intro x y h
  apply Subtype.ext
  have hd := congrArg (decodeBoundary A s) h
  simpa only [decode_encode_boundary] using hd

theorem admissible_boundary_card_le (A : Riffle.Setup D) (s : Riffle.Side) :
    Nat.card {x : Riffle.Word // x ∈ Riffle.Admissible A s} ≤
      (D.K + 1) * (D.k + 1) * sparseCount D.K D.k (boundaryBudget A) := by
  letI : Fintype (BoundaryCode D.K D.k (boundaryBudget A)) := by
    unfold BoundaryCode
    infer_instance
  have h := Finite.card_le_of_injective (encodeBoundary A s) (encodeBoundary_injective A s)
  simpa only [Nat.card_eq_fintype_card, BoundaryCode, Fintype.card_prod,
    Fintype.card_fin, card_sparseAssignment, mul_assoc] using h

def encodePair (A : Riffle.Setup D)
    (p : {p : Riffle.Word × Riffle.Word // Riffle.AdmissiblePair A p.1 p.2}) :
    BoundaryCode D.K D.k (boundaryBudget A) ×
      BoundaryCode D.K D.k (boundaryBudget A) :=
  (encodeBoundary A .left ⟨p.val.1, p.property.1⟩,
    encodeBoundary A .right ⟨p.val.2, p.property.2.1⟩)

theorem encodePair_injective (A : Riffle.Setup D) :
    Function.Injective (encodePair A) := by
  intro p q h
  have hl := encodeBoundary_injective A .left (congrArg Prod.fst h)
  have hr := encodeBoundary_injective A .right (congrArg Prod.snd h)
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val hl) (congrArg Subtype.val hr)

theorem admissible_pair_card_le (A : Riffle.Setup D) :
    Nat.card {p : Riffle.Word × Riffle.Word // Riffle.AdmissiblePair A p.1 p.2} ≤
      ((D.K + 1) * (D.k + 1) * sparseCount D.K D.k (boundaryBudget A)) ^ 2 := by
  letI : Fintype (BoundaryCode D.K D.k (boundaryBudget A)) := by
    unfold BoundaryCode
    infer_instance
  have h := Finite.card_le_of_injective (encodePair A) (encodePair_injective A)
  simpa only [Nat.card_eq_fintype_card, BoundaryCode, Fintype.card_prod,
    Fintype.card_fin, card_sparseAssignment, pow_two, mul_assoc] using h

end

end InhomogeneousShuffle.FirstMoment.Model
