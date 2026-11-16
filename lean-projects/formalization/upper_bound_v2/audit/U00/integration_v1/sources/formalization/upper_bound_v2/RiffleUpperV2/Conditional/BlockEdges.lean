import RiffleUpperV2.Conditional.BlockGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Reservoir TimeProfile RiffleLowerV2

/-- Local cylinder edge shifted to its actual whole-deck edge position. -/
def cylinderEdgePosition {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K) (ω : Sample cuts)
    (e : Fin ((cylinderRows x ω).card-1)) : Fin (n-1) :=
  ⟨lowerRank x ω+e.val,by have := cylinderRank_card cuts x ω; have := e.isLt; omega⟩

theorem cylinderEdge_endpoints {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K) (ω : Sample cuts)
    (e : Fin ((cylinderRows x ω).card-1)) :
    edgeLeft (cylinderEdgePosition cuts x ω e) = cylinderPosition cuts x ω (edgeLeft e) ∧
    edgeRight (cylinderEdgePosition cuts x ω e) = cylinderPosition cuts x ω (edgeRight e) := by
  constructor <;> apply Fin.ext <;> simp [edgeLeft,edgeRight,cylinderPosition,cylinderEdgePosition,Nat.add_assoc]

/-- Membership of a local graph edge is exactly membership of the global
shuffle edge after translating by the actual prefix lower rank. -/
theorem blockEdge_global_iff {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K) (ω : Sample cuts)
    (e : Fin ((cylinderRows x ω).card-1)) :
    e ∈ blockGraph (cylinderRows x ω) ω ↔ cylinderEdgePosition cuts x ω e ∈ shuffleEdges ω := by
  simp only [blockGraph,Model.mem_keyEdges,shuffleEdges,RiffleLowerV2.shuffleEdges,
    Finset.mem_filter,Finset.mem_univ,true_and]
  rw [(cylinderEdge_endpoints cuts x ω e).1,(cylinderEdge_endpoints cuts x ω e).2]
  rw [sortedBlockWord_eq cuts x ω,sortedBlockWord_eq cuts x ω]

theorem absoluteBlockGraph_mem_iff {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K)
    (ω : Sample cuts) (z : ℤ) :
    z ∈ absoluteBlockGraph x ω ↔ ∃ e : Fin (n-1), e ∈ shuffleEdges ω ∧
      z = (e.val : ℤ) ∧ lowerRank x ω ≤ e.val ∧ e.val+1 < upperRank x ω := by
  constructor
  · intro hz
    obtain ⟨e,he,hz⟩ := Finset.mem_image.mp hz
    refine ⟨cylinderEdgePosition cuts x ω e,(blockEdge_global_iff cuts x ω e).mp he,?_,?_,?_⟩
    · change z = ((lowerRank x ω+e.val : ℕ) : ℤ)
      rw [Nat.cast_add]
      exact hz.symm
    · exact Nat.le_add_right _ _
    · have hc := cylinderRank_card cuts x ω
      have he := e.isLt
      dsimp [cylinderEdgePosition]
      omega
  · rintro ⟨e,he,rfl,hlo,hhi⟩
    let a : Fin ((cylinderRows x ω).card-1) := ⟨e.val-lowerRank x ω,by
      have hc := cylinderRank_card cuts x ω; omega⟩
    have ha : cylinderEdgePosition cuts x ω a = e := by
      apply Fin.ext
      dsimp [cylinderEdgePosition,a]
      omega
    apply Finset.mem_image.mpr
    refine ⟨a,(blockEdge_global_iff cuts x ω a).mpr (ha.symm ▸ he),?_⟩
    dsimp [a]
    omega

/-- A global equal-word edge lies in the local cylinder graph precisely when
its word has the cylinder prefix. Both endpoints are included automatically. -/
theorem absoluteBlockGraph_edge_iff {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K)
    (ω : Sample cuts) (e : Fin (n-1)) (he : e ∈ shuffleEdges ω) :
    (e.val : ℤ) ∈ absoluteBlockGraph x ω ↔ inCylinder x (sortedWord ω (edgeLeft e)) := by
  have heq : sortedWord ω (edgeLeft e)=sortedWord ω (edgeRight e) := (Finset.mem_filter.mp he).2
  have hp : ∀ w : Word k K, inCylinder x w ↔ w.toList.take x.1.val=x.2.toList := by
    intro w
    simp only [inCylinder,List.prefix_iff_eq_take,List.Vector.toList_length,eq_comm]
  rw [hp]
  rw [(Model.prefixRanks cuts ω x).1 (edgeLeft e)]
  rw [absoluteBlockGraph_mem_iff]
  constructor
  · rintro ⟨a,ha,hea,hlo,hhi⟩
    have hae : a=e := Fin.ext (by exact_mod_cast hea.symm)
    subst a
    dsimp [edgeLeft]
    simp only [lowerRank,upperRank] at *
    omega
  · intro h
    have hright := (Model.prefixRanks cuts ω x).1 (edgeRight e)
    have hword := ((Model.prefixRanks cuts ω x).1 (edgeLeft e)).mpr h
    change RiffleLowerV2.sortedWord ω (edgeLeft e) = RiffleLowerV2.sortedWord ω (edgeRight e) at heq
    rw [heq] at hword
    have hr := hright.mp hword
    exact ⟨e,he,rfl,h.1,hr.2⟩

end RiffleUpperV2.Conditional
