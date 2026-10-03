import FirstMoment.Counting
import RiffleUpperV2.FirstMoment.Entropy
import RiffleUpperV2.Localization.Boundary

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization
attribute [local instance] Classical.propDecidable
local instance {A : Sort*} : DecidableEq A := Classical.typeDecidableEq A
open InhomogeneousShuffle.FirstMoment (SparseAssignment sparseCount BoundaryCode)

/-- Complete a prefix deterministically; these digits never create extra words. -/
def completePrefix {k d : ℕ} (default : Fin d → Fin k) (x : Prefix k d) : Fin d → Fin k :=
  fun j => if h : j.val < x.1.val then x.2.get ⟨j.val,h⟩ else default j

/-- Every non-default digit strictly before the crossing is recorded. -/
def boundaryExceptions {k d : ℕ} (default : Fin d → Fin k) (x : Prefix k d) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun j => j.val+1 < x.1.val ∧ completePrefix default x j ≠ default j

abbrev BoundedBoundary (k d qb : ℕ) (default : Fin d → Fin k) :=
  {x : Prefix k d // (boundaryExceptions default x).card ≤ qb}

/-- The last digit is stored separately, including a sentinel for the empty prefix. -/
def encodeBoundary {k d qb : ℕ} (default : Fin d → Fin k)
    (x : BoundedBoundary k d qb default) : BoundaryCode d k qb :=
  (x.1.1, (if h : 0 < x.1.1.val then
    ⟨(x.1.2.get ⟨x.1.1.val-1, by omega⟩).val, by
      have := (x.1.2.get ⟨x.1.1.val-1, by omega⟩).isLt; omega⟩ else ⟨k, by omega⟩),
    ⟨⟨boundaryExceptions default x.1,x.2⟩, fun j => completePrefix default x.1 j.1⟩)

def decodeBoundary {k d qb : ℕ} (hk : 0 < k) (default : Fin d → Fin k)
    (c : BoundaryCode d k qb) : Prefix k d :=
  ⟨c.1, List.Vector.ofFn fun i =>
    let j : Fin d := ⟨i.val, by have := c.1.isLt; omega⟩
    if i.val+1 = c.1.val then ⟨c.2.1.val % k, Nat.mod_lt _ hk⟩
    else if h : j ∈ c.2.2.1.1 then c.2.2.2 ⟨j,h⟩ else default j⟩

/-- Exact reconstruction handles terminal and empty boundary prefixes too. -/
theorem decode_encode_boundary {k d qb : ℕ} (hk : 0 < k) (default : Fin d → Fin k)
    (x : BoundedBoundary k d qb default) : decodeBoundary hk default (encodeBoundary default x) = x.1 := by
  classical
  rcases x with ⟨⟨len,x⟩,hx⟩
  dsimp only [decodeBoundary, encodeBoundary]
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply List.Vector.ext
  intro i
  have hiLt : i.val < len.val := i.isLt
  have hlen : 0 < len.val := by omega
  simp only [List.Vector.get_ofFn, dif_pos hlen]
  by_cases hlast : i.val+1 = len.val
  · simp only [if_pos hlast]
    apply Fin.ext
    change (x.get ⟨len.val-1,by omega⟩).val % k = (x.get i).val
    rw [Nat.mod_eq_of_lt (x.get ⟨len.val-1,by omega⟩).isLt]
    congr 2
    apply Fin.ext
    change len.val-1 = i.val
    omega
  · simp only [if_neg hlast]
    let j : Fin d := ⟨i.val, by have := len.isLt; omega⟩
    by_cases hmem : j ∈ boundaryExceptions default ⟨len,x⟩
    · simp only [show (⟨i.val,by omega⟩ : Fin d) = j from rfl, dif_pos hmem]
      simp [completePrefix, j, hiLt]
    · simp only [show (⟨i.val,by omega⟩ : Fin d) = j from rfl, dif_neg hmem]
      have hbefore : i.val+1 < len.val := by omega
      have hnot : ¬ completePrefix default ⟨len,x⟩ j ≠ default j := by
        simpa only [boundaryExceptions, Finset.mem_filter, Finset.mem_univ, true_and,
          show j.val+1 < len.val from hbefore, true_and] using hmem
      simpa [completePrefix, j, hiLt] using (not_not.mp hnot).symm

theorem encodeBoundary_injective {k d qb : ℕ} (hk : 0 < k) (default : Fin d → Fin k) :
    Function.Injective (encodeBoundary (qb := qb) default) := by
  intro x y h
  apply Subtype.ext
  calc
    x.1 = decodeBoundary hk default (encodeBoundary default x) :=
      (decode_encode_boundary hk default x).symm
    _ = decodeBoundary hk default (encodeBoundary default y) := by rw [h]
    _ = y.1 := decode_encode_boundary hk default y

theorem boundary_card_le {k d qb : ℕ} (hk : 0 < k) (default : Fin d → Fin k) :
    Fintype.card (BoundedBoundary k d qb default) ≤
      (d+1)*(k+1)*sparseCount d k qb := by
  classical
  let : Fintype (BoundaryCode d k qb) := by unfold BoundaryCode; infer_instance
  have h := Fintype.card_le_of_injective _ (encodeBoundary_injective (qb := qb) hk default)
  simpa only [BoundaryCode, Fintype.card_prod, Fintype.card_fin,
    InhomogeneousShuffle.FirstMoment.card_sparseAssignment, mul_assoc] using h

/-- An empirical descriptor includes the first pile and both complete boundary
records; the route stores proper/immediate and large/small flags. -/
def EmpiricalKey (k d qb qe bins : ℕ) :=
  Fin k × BoundaryCode d k qb × BoundaryCode d k qb × Fin (d+1) ×
    SparseAssignment d k qe × Fin bins × Fin 4

instance (k d qb qe bins : ℕ) : Fintype (EmpiricalKey k d qb qe bins) := by
  unfold EmpiricalKey BoundaryCode
  infer_instance

/-- Exact key-space cardinality; no boundary or routing multiplicity is omitted. -/
theorem card_empiricalKey (k d qb qe bins : ℕ) :
    Fintype.card (EmpiricalKey k d qb qe bins) =
      4*k*(k+1)^2*(d+1)^3*sparseCount d k qb^2*sparseCount d k qe*bins := by
  simp only [EmpiricalKey, BoundaryCode, Fintype.card_prod, Fintype.card_fin,
    InhomogeneousShuffle.FirstMoment.card_sparseAssignment]
  ring

/-- An extension's actual exceptional set and selected digit values. -/
def encodeExceptions {k n d qe : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (I : Finset (Fin d)) (chi : ℝ) (w : Fin d → Fin k)
    (hq : (exceptionalPositions (cuts.profile hn) I chi w).card ≤ qe) :
    SparseAssignment d k qe :=
  ⟨⟨exceptionalPositions (cuts.profile hn) I chi w,hq⟩, fun j => w j.1⟩

/-- The full finite descriptor is computed from selected digits and costs. -/
def empiricalDescriptor {k n d qb qe bins N : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (leftDefault rightDefault : Fin d → Fin k)
    (pile : Fin k) (y : BoundedBoundary k d qb leftDefault)
    (z : BoundedBoundary k d qb rightDefault) (x : Prefix k d)
    (chi width delta : ℝ) (R : Finset (Fin n))
    (hq : (exceptionalPositions (cuts.profile hn)
      (empiricalPositions d 0 (boundaryJoin y.1 z.1).1.val x.1.val) chi
      (completePrefix leftDefault x)).card ≤ qe)
    (hb : ⌊goodCost N (cuts.profile hn)
      (empiricalPositions d 0 (boundaryJoin y.1 z.1).1.val x.1.val) chi
      (completePrefix leftDefault x)/width⌋₊ < bins) : EmpiricalKey k d qb qe bins :=
  (pile, encodeBoundary leftDefault y, encodeBoundary rightDefault z, x.1,
    encodeExceptions cuts hn
      (empiricalPositions d 0 (boundaryJoin y.1 z.1).1.val x.1.val) chi
      (completePrefix leftDefault x) hq,
    ⟨⌊goodCost N (cuts.profile hn)
      (empiricalPositions d 0 (boundaryJoin y.1 z.1).1.val x.1.val) chi
      (completePrefix leftDefault x)/width⌋₊,hb⟩,
    ⟨(if x.1.val = (boundaryJoin y.1 z.1).1.val then 0 else 2)+
      (if 2*delta ≤ meanExponent N cuts R x then 1 else 0), by split_ifs <;> omega⟩)

/-- Any realized descriptor image obeys the full, explicit finite bound.
The source's N^epsilon asymptotic is a separate remaining obligation. -/
theorem empiricalDescriptorImage_card_le {A : Type*} [Fintype A]
    {k d qb qe bins : ℕ} (descriptor : A → EmpiricalKey k d qb qe bins) :
    (Finset.univ.image descriptor).card ≤
      4*k*(k+1)^2*(d+1)^3*sparseCount d k qb^2*sparseCount d k qe*bins := by
  classical
  rw [← card_empiricalKey]
  exact Finset.card_le_univ _

end RiffleUpperV2.FirstMoment
