import RiffleUpperV2.Reservoir.History
import RiffleUpperV2.Shared.UniformProjection

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile

/-- An induced column consists of all assignments on the specified labeled
rows with precisely their observed color counts. -/
def InteriorColumn {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k) :=
  {q : R → Fin k // ∀ a, (Finset.univ.filter fun r => q r=a).card=(R.filter fun r => c r=a).card}

instance {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k) : Fintype (InteriorColumn R c) := by
  unfold InteriorColumn
  infer_instance

theorem restriction_card {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k) (a : Fin k) :
    (Finset.univ.filter fun r : R => c r.val=a).card=(R.filter fun r => c r=a).card := by
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    exact Finset.mem_filter.mpr ⟨r.property,(Finset.mem_filter.mp hr).2⟩
  · intro r _ s _ hrs
    exact Subtype.ext hrs
  · intro r hr
    exact ⟨⟨r,(Finset.mem_filter.mp hr).1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2⟩,rfl⟩

def interiorRestriction {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k) : InteriorColumn R c :=
  ⟨fun r => c r.val,restriction_card R c⟩

instance {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k) : Nonempty (InteriorColumn R c) :=
  ⟨interiorRestriction R c⟩

def patchValues {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k) (q : R → Fin k) : Fin n → Fin k :=
  fun r => if h : r∈R then q ⟨r,h⟩ else c r

@[simp] theorem patchValues_inside {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k)
    (q : R → Fin k) (r : R) : patchValues R c q r.val=q r := by
  simp only [patchValues,dif_pos r.property]

@[simp] theorem patchValues_outside {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k)
    (q : R → Fin k) (r : Fin n) (hr : r∉R) : patchValues R c q r=c r := by
  simp only [patchValues,dif_neg hr]

theorem column_count_partition {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k) (a : Fin k) :
    (Finset.univ.filter fun r => c r=a).card=
      (R.filter fun r => c r=a).card+((Finset.univ\R).filter fun r => c r=a).card := by
  have he : (Finset.univ.filter fun r => c r=a)=
      (R.filter fun r => c r=a) ∪ ((Finset.univ\R).filter fun r => c r=a) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_sdiff]
    tauto
  rw [he,Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro r hr hs
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).1).2 (Finset.mem_filter.mp hr).1

theorem patchValues_count {k n : ℕ} (R : Finset (Fin n)) (c : Fin n → Fin k)
    (q : InteriorColumn R c) (a : Fin k) :
    (Finset.univ.filter fun r => patchValues R c q.val r=a).card=(Finset.univ.filter fun r => c r=a).card := by
  rw [column_count_partition R, column_count_partition R c]
  congr 1
  · rw [← restriction_card R (patchValues R c q.val) a]
    simpa only [patchValues_inside] using q.property a
  · apply congrArg Finset.card
    apply Finset.filter_congr
    intro r hr
    rw [patchValues_outside R c q.val r (Finset.mem_sdiff.mp hr).2]

/-- Actual global fixed-count column obtained by replacing only the interior. -/
def patchColumn {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d} (R : Finset (Fin n))
    (c : ColumnAssignments cuts j) (q : InteriorColumn R c.val) : ColumnAssignments cuts j :=
  ⟨patchValues R c.val q.val,fun a => (patchValues_count R c.val q a).trans (c.property a)⟩

/-- Full information outside R leaves exactly the induced-count column on R. -/
def interiorColumnEquiv {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d} (R : Finset (Fin n))
    (c₀ : ColumnAssignments cuts j) :
    {c : ColumnAssignments cuts j // ∀ r, r∉R → c.val r=c₀.val r} ≃ InteriorColumn R c₀.val where
  toFun c := ⟨fun r => c.val.val r.val,by
    intro a
    rw [restriction_card]
    have hc := column_count_partition R c.val.val a
    have h0 := column_count_partition R c₀.val a
    rw [c.val.property a] at hc
    rw [c₀.property a] at h0
    have ho : ((Finset.univ\R).filter fun r => c.val.val r=a)=
        ((Finset.univ\R).filter fun r => c₀.val r=a) := by
      apply Finset.filter_congr
      intro r hr
      rw [c.property r (Finset.mem_sdiff.mp hr).2]
    rw [ho] at hc
    omega⟩
  invFun q := ⟨patchColumn R c₀ q,fun r hr => patchValues_outside R c₀.val q.val r hr⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext r
    change patchValues R c₀.val (fun r : R => c.val.val r.val) r=c.val.val r
    by_cases hr : r∈R
    · simp only [patchValues,dif_pos hr]
    · simp only [patchValues,dif_neg hr]
      exact (c.property r hr).symm
  right_inv q := by
    apply Subtype.ext
    funext r
    exact patchValues_inside R c₀.val q.val r

end RiffleUpperV2.Reservoir
