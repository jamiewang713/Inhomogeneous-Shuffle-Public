import FirstMomentModel.BoundaryEncoding
import Riffle.SourceStable
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Realized refined profile classes from the frozen supplemental contract.
The domain retains the source real cutoff; only its consequence is rounded.
-/

namespace InhomogeneousShuffle.FirstMoment.Model

noncomputable section

variable {D : Riffle.Model} {c : ℕ}

def exceptionalPositions (A : Riffle.Setup D) (good : Fin D.K → ℕ → Prop)
    (y z x : Riffle.Word) : Finset (Fin D.K) := by
  classical
  exact Finset.univ.filter (fun i => (Riffle.join y z).length ≤ i.val ∧
    i.val < x.length ∧ ¬good i (Riffle.digit x i.val))

def goodDigitCount (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (y z x : Riffle.Word)
    (a : Fin c) (l : Fin D.k) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin D.K =>
    (Riffle.join y z).length ≤ i.val ∧ i.val < x.length ∧
      cell i = a ∧ Riffle.digit x i.val = l.val ∧
      good i (Riffle.digit x i.val))).card

def exceptionalBudget (A : Riffle.Setup D) (alpha : ℝ) : ℕ :=
  Nat.floor (alpha * Real.log (D.N : ℝ))

def ProfileWord (A : Riffle.Setup D) (good : Fin D.K → ℕ → Prop)
    (alpha : ℝ) : Type :=
  {p : Riffle.Word × Riffle.Word × Riffle.Word //
    Riffle.AdmissiblePair A p.1 p.2.1 ∧ p.2.2 ∈ Riffle.Stable A p.1 p.2.1 ∧
      ((exceptionalPositions A good p.1 p.2.1 p.2.2).card : ℝ) ≤
        alpha * Real.log (D.N : ℝ)}

theorem profileWord_exceptional_budget (A : Riffle.Setup D)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ) (p : ProfileWord A good alpha) :
    (exceptionalPositions A good p.val.1 p.val.2.1 p.val.2.2).card ≤
      exceptionalBudget A alpha :=
  Nat.le_floor p.property.2.2

theorem goodDigitCount_le (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (y z x : Riffle.Word)
    (a : Fin c) (l : Fin D.k) : goodDigitCount A cell good y z x a l ≤ D.K := by
  classical
  unfold goodDigitCount
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

def encodeProfile (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4) (p : ProfileWord A good alpha) :
    ProfileKey D.K D.k (boundaryBudget A) (exceptionalBudget A alpha) (c * D.k) := by
  classical
  have hp : Riffle.AdmissiblePair A p.val.1 p.val.2.1 := p.property.1
  have hx : Riffle.Legal D p.val.2.2 :=
    (Riffle.stable_desc (Riffle.admissiblePair_rawPair hp) p.property.2.1).1
  refine ⟨encodeBoundary A .left ⟨p.val.1, hp.1⟩,
    encodeBoundary A .right ⟨p.val.2.1, hp.2.1⟩,
    ⟨p.val.2.2.length, Nat.lt_succ_of_le hx.1⟩, ?_, ?_, route p⟩
  · intro h
    let al : Fin c × Fin D.k := finProdFinEquiv.symm h
    exact ⟨goodDigitCount A cell good p.val.1 p.val.2.1 p.val.2.2 al.1 al.2,
      Nat.lt_succ_of_le (goodDigitCount_le A cell good _ _ _ al.1 al.2)⟩
  · refine ⟨⟨exceptionalPositions A good p.val.1 p.val.2.1 p.val.2.2,
      profileWord_exceptional_budget A good alpha p⟩, ?_⟩
    intro i
    have hi : i.val.val < p.val.2.2.length := (Finset.mem_filter.mp i.property).2.2.1
    exact ⟨Riffle.digit p.val.2.2 i.val.val, (hx.2 _ hi).1⟩

def ProfileClass (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4) : Type :=
  ↥(Set.range (encodeProfile A cell good alpha route))

theorem encodeProfile_eq_data (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4) (p q : ProfileWord A good alpha)
    (h : encodeProfile A cell good alpha route p = encodeProfile A cell good alpha route q) :
    p.val.1 = q.val.1 ∧
      p.val.2.1 = q.val.2.1 ∧
      p.val.2.2.length = q.val.2.2.length ∧
      (∀ a : Fin c, ∀ l : Fin D.k,
        goodDigitCount A cell good p.val.1 p.val.2.1 p.val.2.2 a l =
          goodDigitCount A cell good q.val.1 q.val.2.1 q.val.2.2 a l) ∧
      exceptionalPositions A good p.val.1 p.val.2.1 p.val.2.2 =
        exceptionalPositions A good q.val.1 q.val.2.1 q.val.2.2 ∧
      (∀ i ∈ exceptionalPositions A good p.val.1 p.val.2.1 p.val.2.2,
        Riffle.digit p.val.2.2 i.val = Riffle.digit q.val.2.2 i.val) ∧
      route p = route q := by
  classical
  let Key := ProfileKey D.K D.k (boundaryBudget A) (exceptionalBudget A alpha) (c * D.k)
  have hl : encodeBoundary A .left ⟨p.val.1, p.property.1.1⟩ =
      encodeBoundary A .left ⟨q.val.1, q.property.1.1⟩ := congrArg Prod.fst h
  have hr : encodeBoundary A .right ⟨p.val.2.1, p.property.1.2.1⟩ =
      encodeBoundary A .right ⟨q.val.2.1, q.property.1.2.1⟩ :=
    congrArg (fun key : Key => key.2.1) h
  have hy : p.val.1 = q.val.1 :=
    congrArg Subtype.val (encodeBoundary_injective A .left hl)
  have hz : p.val.2.1 = q.val.2.1 :=
    congrArg Subtype.val (encodeBoundary_injective A .right hr)
  have hlen : p.val.2.2.length = q.val.2.2.length :=
    congrArg (fun key : Key => key.2.2.1.val) h
  have hcounts : ∀ a : Fin c, ∀ l : Fin D.k,
      goodDigitCount A cell good p.val.1 p.val.2.1 p.val.2.2 a l =
        goodDigitCount A cell good q.val.1 q.val.2.1 q.val.2.2 a l := by
    intro a l
    have hc := congrArg (fun key : Key => (key.2.2.2.1 (finProdFinEquiv (a, l))).val) h
    simpa only [encodeProfile, Equiv.symm_apply_apply] using hc
  have hsparse : (encodeProfile A cell good alpha route p).2.2.2.2.1 =
      (encodeProfile A cell good alpha route q).2.2.2.2.1 :=
    congrArg (fun key : Key => key.2.2.2.2.1) h
  have hpositions : exceptionalPositions A good p.val.1 p.val.2.1 p.val.2.2 =
      exceptionalPositions A good q.val.1 q.val.2.1 q.val.2.2 :=
    congrArg (fun e : SparseAssignment D.K D.k (exceptionalBudget A alpha) => e.1.val) hsparse
  have hdigits : ∀ i ∈ exceptionalPositions A good p.val.1 p.val.2.1 p.val.2.2,
      Riffle.digit p.val.2.2 i.val = Riffle.digit q.val.2.2 i.val := by
    intro i hi
    have hiq : i ∈ exceptionalPositions A good q.val.1 q.val.2.1 q.val.2.2 :=
      hpositions ▸ hi
    let lookup : SparseAssignment D.K D.k (exceptionalBudget A alpha) → Fin D.K → ℕ :=
      fun e j => if hj : j ∈ e.1.val then (e.2 ⟨j, hj⟩).val else D.k
    have he := congrArg (fun e => lookup e i) hsparse
    simpa only [encodeProfile, lookup, dif_pos hi, dif_pos hiq] using he
  have hroute : route p = route q := congrArg (fun key : Key => key.2.2.2.2.2) h
  exact ⟨hy, hz, hlen, hcounts, hpositions, hdigits, hroute⟩

theorem profileClass_card_le (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4) :
    Nat.card (ProfileClass A cell good alpha route) ≤
      profileCountBound D.K D.k (boundaryBudget A) (exceptionalBudget A alpha) (c * D.k) := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : ProfileClass A cell good alpha route →
      ProfileKey D.K D.k (boundaryBudget A) (exceptionalBudget A alpha) (c * D.k))
    Subtype.val_injective
  simpa only [ProfileClass, Nat.card_eq_fintype_card, card_profileKey] using h

end

end InhomogeneousShuffle.FirstMoment.Model
