import RiffleUpperV2.Reservoir.InteriorHistory
import RiffleUpperV2.Reservoir.InteriorProjection

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

/-- Global fixed counts and unchanged exterior entries force every induced
interior column count to remain unchanged. -/
theorem interior_counts_eq {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber R J ω₀ ω) (j : Fin d) (a : Fin k) :
    (R.filter fun r => sampleEntry ω r j=a).card=(R.filter fun r => sampleEntry ω₀ r j=a).card := by
  have h1 := column_count_partition R (ω j).val a
  have h0 := column_count_partition R (ω₀ j).val a
  rw [(ω j).property a] at h1
  rw [(ω₀ j).property a] at h0
  have ho : ((Finset.univ\R).filter fun r => (ω j).val r=a)=
      ((Finset.univ\R).filter fun r => (ω₀ j).val r=a) := by
    apply Finset.filter_congr
    intro r hr
    have hh := h j r (Or.inr (Finset.mem_sdiff.mp hr).2)
    simpa only [sampleEntry] using (Iff.of_eq (congrArg (fun z : Fin k => z=a) hh))
  rw [ho] at h1
  change (R.filter fun r => (ω j).val r=a).card=(R.filter fun r => (ω₀ j).val r=a).card
  omega

theorem interior_lowerRank_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (R : Finset (Fin n)) (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber R (tailColumns x) ω₀ ω) : lowerRank x ω=lowerRank x ω₀ := by
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r _
  rw [interior_prefix_eq cuts x R ω₀ ω h r]

theorem interior_upperRank_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (R : Finset (Fin n)) (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber R (tailColumns x) ω₀ ω) : upperRank x ω=upperRank x ω₀ := by
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r _
  rw [interior_prefix_eq cuts x R ω₀ ω h r]

/-- The literal data attached to a cylinder: labeled rows, absolute rank
interval, and every induced column count. Prefix-column counts are redundant. -/
def cylinderRecord {k n d : ℕ} {cuts : Cuts k n d} (x : Prefix k d) (ω : Sample cuts) :=
  (cylinderRows x ω, lowerRank x ω, upperRank x ω,
    fun j : Fin d => fun a : Fin k => ((cylinderRows x ω).filter fun r => sampleEntry ω r j=a).card)

theorem interior_cylinderRecord_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber (cylinderRows x ω₀) (tailColumns x) ω₀ ω) :
    cylinderRecord x ω=cylinderRecord x ω₀ := by
  have hR := interior_cylinderRows_eq cuts x _ ω₀ ω h
  unfold cylinderRecord
  rw [hR,interior_lowerRank_eq cuts x _ ω₀ ω h,interior_upperRank_eq cuts x _ ω₀ ω h]
  congr 3
  funext j a
  exact interior_counts_eq cuts _ _ ω₀ ω h j a

end RiffleUpperV2.Reservoir
