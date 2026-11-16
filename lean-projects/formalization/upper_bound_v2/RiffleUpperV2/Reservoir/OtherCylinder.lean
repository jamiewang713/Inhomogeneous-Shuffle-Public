import RiffleUpperV2.Reservoir.SeparatedCylinders

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

theorem interior_other_comparison {k n d : ℕ} (cuts : Cuts k n d) (x y : Prefix k d)
    (hsep : prefixSeparated x y) (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber (cylinderRows x ω₀) (tailColumns x) ω₀ ω) (r : Fin n) :
    (((rowWord ω r).toList.take y.1.val<y.2.toList) ↔ ((rowWord ω₀ r).toList.take y.1.val<y.2.toList)) ∧
    (((rowWord ω r).toList.take y.1.val≤y.2.toList) ↔ ((rowWord ω₀ r).toList.take y.1.val≤y.2.toList)) ∧
    (((rowWord ω r).toList.take y.1.val=y.2.toList) ↔ ((rowWord ω₀ r).toList.take y.1.val=y.2.toList)) := by
  by_cases hr : r∈cylinderRows x ω₀
  · have h0 := (Finset.mem_filter.mp hr).2
    have h1 := (interior_prefix_eq cuts x _ ω₀ ω h r).trans h0
    exact separated_prefix_comparison x y hsep (rowWord ω r) (rowWord ω₀ r) h1 h0
  · rw [interior_outside_word cuts _ _ ω₀ ω h r hr]
    exact ⟨Iff.rfl,Iff.rfl,Iff.rfl⟩

/-- Every record of every disjoint cylinder survives a replacement in x,
including absolute ranks and its own induced tail counts. -/
theorem interior_other_record_eq {k n d : ℕ} (cuts : Cuts k n d) (x y : Prefix k d)
    (hsep : prefixSeparated x y) (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber (cylinderRows x ω₀) (tailColumns x) ω₀ ω) :
    cylinderRecord y ω=cylinderRecord y ω₀ := by
  have hR : cylinderRows y ω=cylinderRows y ω₀ := by
    apply Finset.filter_congr
    intro r _
    exact (interior_other_comparison cuts x y hsep ω₀ ω h r).2.2
  have hlo : lowerRank y ω=lowerRank y ω₀ := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro r _
    exact (interior_other_comparison cuts x y hsep ω₀ ω h r).1
  have hhi : upperRank y ω=upperRank y ω₀ := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro r _
    exact (interior_other_comparison cuts x y hsep ω₀ ω h r).2.1
  unfold cylinderRecord
  rw [hR,hlo,hhi]
  congr 3
  funext j a
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r hr
  have hrx : r∉cylinderRows x ω₀ := by
    intro hx
    exact prefixSeparated_not_both x y hsep (rowWord ω₀ r) (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hr).2
  have he := h j r (Or.inr hrx)
  exact Iff.of_eq (congrArg (fun z : Fin k => z=a) he)

end RiffleUpperV2.Reservoir
