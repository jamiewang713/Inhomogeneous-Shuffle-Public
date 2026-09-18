import RiffleProfiles.BoundaryTruncation
import RiffleProfiles.Counting
import Mathlib.SetTheory.Cardinal.Finite

/-!
Frozen T05: actual admissible boundary prefixes are encoded by relative
length, their final digit, and labelled violations before the final digit.
-/

set_option autoImplicit false

noncomputable section

namespace RiffleProfiles

variable {D : Riffle.Model}

private def boundaryViolation (A : Riffle.Setup D) (side : Riffle.Side)
    (x : Riffle.Word) (i : ℕ) : Prop :=
  match side with
  | .left => Riffle.digit x i < Riffle.leftIndex A i
  | .right => Riffle.rightIndex A i < Riffle.digit x i

private def boundaryExtreme (A : Riffle.Setup D) (side : Riffle.Side) (i : ℕ) : ℕ :=
  match side with
  | .left => Riffle.leftIndex A i
  | .right => Riffle.rightIndex A i

private theorem boundary_no_earlier_cross (A : Riffle.Setup D) (side : Riffle.Side)
    {x : Riffle.Word} (hx : x ∈ Riffle.Boundary A side) {i : ℕ}
    (hwi : A.w.length ≤ i) (hix : i < x.length - 1) :
    ¬ Riffle.Cross A side x i := by
  rcases hx.2 with hc | ht
  · exact hc.2.2 i hwi hix
  · exact ht.2 i hwi (by omega)

private theorem boundary_forced_extreme (A : Riffle.Setup D) (side : Riffle.Side)
    {x : Riffle.Word} (hx : x ∈ Riffle.Boundary A side) {i : ℕ}
    (hwi : A.w.length ≤ i) (hix : i < x.length - 1)
    (hvi : ¬ boundaryViolation A side x i) :
    Riffle.digit x i = boundaryExtreme A side i := by
  have hn := boundary_no_earlier_cross A side hx hwi hix
  cases side <;>
    simp only [Riffle.Cross, Riffle.crossDigit, boundaryViolation, boundaryExtreme] at * <;>
    omega

/-- The frozen relative support, excluding the separately recorded final digit. -/
def boundarySparseSupport (A : Riffle.Setup D) (side : Riffle.Side)
    (x : Riffle.Word) : Finset (Fin D.K) := by
  classical
  exact Finset.univ.filter fun t =>
    t.val + 1 < x.length - A.w.length ∧
      boundaryViolation A side x (A.w.length + t.val)

private theorem boundarySparseSupport_card_le (A : Riffle.Setup D) (side : Riffle.Side)
    {x : Riffle.Word} (_hx : x ∈ Riffle.Boundary A side) :
    (boundarySparseSupport A side x).card ≤ Riffle.violations A side x := by
  classical
  let shift : Fin D.K → ℕ := fun t => A.w.length + t.val
  have hinj : Function.Injective shift := by
    intro t u htu
    apply Fin.ext
    exact Nat.add_left_cancel htu
  have hsub : (boundarySparseSupport A side x).image shift ⊆
      (Finset.Ico A.w.length x.length).filter (boundaryViolation A side x) := by
    intro i hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
    have ht' := (Finset.mem_filter.mp ht).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ?_, ht'.2⟩
    dsimp [shift]
    omega
  calc
    (boundarySparseSupport A side x).card =
        ((boundarySparseSupport A side x).image shift).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((Finset.Ico A.w.length x.length).filter (boundaryViolation A side x)).card :=
      Finset.card_le_card hsub
    _ = Riffle.violations A side x := by cases side <;> rfl

private theorem admissible_violations_le_floor (A : Riffle.Setup D) (side : Riffle.Side)
    {x : Riffle.Word} (hx : x ∈ Riffle.Admissible A side) :
    Riffle.violations A side x ≤ Nat.floor (boundaryThreshold A) := by
  apply Nat.le_floor
  exact hx.2

private def boundaryFinalDigit (A : Riffle.Setup D) (side : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A side}) : Fin D.k :=
  if hm : x.val.length - A.w.length = 0 then
    ⟨0, by have hk := D.two_le_k; omega⟩
  else
    ⟨Riffle.digit x.val (x.val.length - 1),
      (x.property.1.1.1.2 (x.val.length - 1) (by omega)).1⟩

private def admissibleBoundaryPattern (A : Riffle.Setup D) (side : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A side}) :
    SparsePattern D.K (Nat.floor (boundaryThreshold A)) D.k := by
  classical
  refine ⟨⟨boundarySparseSupport A side x.val, ?_⟩, ?_⟩
  · exact (boundarySparseSupport_card_le A side x.property.1).trans
      (admissible_violations_le_floor A side x.property)
  · intro t
    refine ⟨Riffle.digit x.val (A.w.length + t.val.val), ?_⟩
    apply (x.property.1.1.1.2 (A.w.length + t.val.val) ?_).1
    have ht := (Finset.mem_filter.mp t.property).2.1
    omega

/-- T05's actual relative descriptor, including the final digit of terminal fallback. -/
def admissibleBoundaryDescriptor (A : Riffle.Setup D) (side : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A side}) :
    BoundaryDescriptor D.K (Nat.floor (boundaryThreshold A)) D.k := by
  classical
  refine ⟨(⟨x.val.length - A.w.length, ?_⟩,
    boundaryFinalDigit A side x, admissibleBoundaryPattern A side x), ?_⟩
  · have hxK := x.property.1.1.1.1
    omega
  · constructor
    · intro t ht
      exact (Finset.mem_filter.mp ht).2.1
    · intro hm
      change x.val.length - A.w.length = 0 at hm
      simp only [boundaryFinalDigit, hm, ↓reduceDIte]

private def descriptorRecordedDigit {K h k : ℕ} (d : BoundaryDescriptor K h k)
    (t : Fin K) (fallback : ℕ) : ℕ := by
  classical
  exact if ht : t ∈ d.val.2.2.1.val then (d.val.2.2.2 ⟨t, ht⟩).val else fallback

private theorem descriptor_prefinal_digit (A : Riffle.Setup D) (side : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A side}) (t : Fin D.K)
    (ht : t.val + 1 < x.val.length - A.w.length) :
    descriptorRecordedDigit (admissibleBoundaryDescriptor A side x) t
        (boundaryExtreme A side (A.w.length + t.val)) =
      Riffle.digit x.val (A.w.length + t.val) := by
  classical
  change (if _ht : t ∈ boundarySparseSupport A side x.val then
    Riffle.digit x.val (A.w.length + t.val)
    else boundaryExtreme A side (A.w.length + t.val)) = _
  split_ifs with hs
  · rfl
  · apply (boundary_forced_extreme A side x.property.1 (by omega) (by omega) ?_).symm
    intro hvi
    apply hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hvi⟩

private theorem descriptor_final_digit (A : Riffle.Setup D) (side : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A side})
    (hm : x.val.length - A.w.length ≠ 0) :
    (admissibleBoundaryDescriptor A side x).val.2.1.val =
      Riffle.digit x.val (x.val.length - 1) := by
  simp only [admissibleBoundaryDescriptor, boundaryFinalDigit, hm, ↓reduceDIte]

/-- T05: every actual admissible boundary is uniquely recovered from its descriptor. -/
theorem admissibleBoundaryDescriptor_injective (A : Riffle.Setup D) (side : Riffle.Side) :
    Function.Injective (admissibleBoundaryDescriptor A side) := by
  intro x y hxy
  have hext : x.val.length - A.w.length = y.val.length - A.w.length :=
    congrArg (fun d => d.val.1.val) hxy
  have hwx : A.w.length ≤ x.val.length := x.property.1.1.2.length_le
  have hwy : A.w.length ≤ y.val.length := y.property.1.1.2.length_le
  have hlen : x.val.length = y.val.length := by omega
  have hdigit : ∀ i, i < x.val.length → Riffle.digit x.val i = Riffle.digit y.val i := by
    intro i hi
    by_cases hwi : i < A.w.length
    · exact (Riffle.digit_prefix x.property.1.1.2 hwi).symm.trans
        (Riffle.digit_prefix y.property.1.1.2 hwi)
    · have hwi' : A.w.length ≤ i := by omega
      by_cases hlast : i = x.val.length - 1
      · have hmx : x.val.length - A.w.length ≠ 0 := by omega
        have hmy : y.val.length - A.w.length ≠ 0 := by omega
        have hfinal := congrArg (fun d => d.val.2.1.val) hxy
        dsimp only at hfinal
        rw [descriptor_final_digit A side x hmx, descriptor_final_digit A side y hmy] at hfinal
        simpa only [hlast, hlen] using hfinal
      · have hxK : x.val.length ≤ D.K := x.property.1.1.1.1
        let t : Fin D.K := ⟨i - A.w.length, by omega⟩
        have ht : t.val + 1 < x.val.length - A.w.length := by dsimp [t]; omega
        have ht' : t.val + 1 < y.val.length - A.w.length := by omega
        have heq := congrArg
          (fun d => descriptorRecordedDigit d t (boundaryExtreme A side (A.w.length + t.val))) hxy
        dsimp only at heq
        rw [descriptor_prefinal_digit A side x t ht,
          descriptor_prefinal_digit A side y t ht'] at heq
        have hti : A.w.length + t.val = i := by dsimp [t]; omega
        simpa only [hti] using heq
  apply Subtype.ext
  apply List.ext_getElem
  · exact hlen
  · intro i hix hiy
    simpa only [Riffle.digit, List.getElem?_eq_getElem hix,
      List.getElem?_eq_getElem hiy, Option.getD_some] using hdigit i hix

/-- T05: finiteness is derived from the descriptor injection. -/
instance admissibleBoundaryFinite (A : Riffle.Setup D) (side : Riffle.Side) :
    Finite {x : Riffle.Word // x ∈ Riffle.Admissible A side} :=
  Finite.of_injective _ (admissibleBoundaryDescriptor_injective A side)

/-- T05: the actual admissible boundary cardinality has the frozen finite bound. -/
theorem admissibleBoundary_card_le (A : Riffle.Setup D) (side : Riffle.Side) :
    Nat.card {x : Riffle.Word // x ∈ Riffle.Admissible A side} ≤
      D.k * (D.K + 1) * lowCount D.K (Nat.floor (boundaryThreshold A)) D.k := by
  calc
    Nat.card {x : Riffle.Word // x ∈ Riffle.Admissible A side} ≤
        Nat.card (BoundaryDescriptor D.K (Nat.floor (boundaryThreshold A)) D.k) :=
      Nat.card_le_card_of_injective _ (admissibleBoundaryDescriptor_injective A side)
    _ ≤ _ := by
      rw [Nat.card_eq_fintype_card]
      exact boundaryDescriptor_card_le _ _ _ D.two_le_k

private def admissiblePairComponents (A : Riffle.Setup D)
    (p : {yz : Riffle.Word × Riffle.Word // Riffle.AdmissiblePair A yz.1 yz.2}) :
    {x : Riffle.Word // x ∈ Riffle.Admissible A .left} ×
      {x : Riffle.Word // x ∈ Riffle.Admissible A .right} :=
  (⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2.1⟩)

private theorem admissiblePairComponents_injective (A : Riffle.Setup D) :
    Function.Injective (admissiblePairComponents A) := by
  intro x y hxy
  apply Subtype.ext
  exact Prod.ext (congrArg (fun p => p.1.val) hxy) (congrArg (fun p => p.2.val) hxy)

/-- T05: compatible admissible pairs form a finite subtype. -/
instance admissiblePairFinite (A : Riffle.Setup D) :
    Finite {yz : Riffle.Word × Riffle.Word // Riffle.AdmissiblePair A yz.1 yz.2} :=
  Finite.of_injective _ (admissiblePairComponents_injective A)

/-- T05: compatibility can only reduce the product of the two boundary counts. -/
theorem admissiblePair_card_le (A : Riffle.Setup D) :
    Nat.card {yz : Riffle.Word × Riffle.Word // Riffle.AdmissiblePair A yz.1 yz.2} ≤
      (D.k * (D.K + 1) * lowCount D.K (Nat.floor (boundaryThreshold A)) D.k) ^ 2 := by
  calc
    Nat.card {yz : Riffle.Word × Riffle.Word // Riffle.AdmissiblePair A yz.1 yz.2} ≤
        Nat.card ({x : Riffle.Word // x ∈ Riffle.Admissible A .left} ×
          {x : Riffle.Word // x ∈ Riffle.Admissible A .right}) :=
      Nat.card_le_card_of_injective _ (admissiblePairComponents_injective A)
    _ = Nat.card {x : Riffle.Word // x ∈ Riffle.Admissible A .left} *
        Nat.card {x : Riffle.Word // x ∈ Riffle.Admissible A .right} := Nat.card_prod _ _
    _ ≤ _ := by
      simpa only [pow_two] using Nat.mul_le_mul
        (admissibleBoundary_card_le A .left) (admissibleBoundary_card_le A .right)

end RiffleProfiles
