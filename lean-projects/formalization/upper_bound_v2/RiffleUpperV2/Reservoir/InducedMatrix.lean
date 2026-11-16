import RiffleUpperV2.Reservoir.FutureCylinderLaw
import RiffleUpperV2.Reservoir.ExposedRows

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration

def suffixColumn {k d : ℕ} (x : Prefix k d) (j : Fin (d-x.1.val)) : Fin d :=
  ⟨x.1.val+j.val,by have := j.isLt; have := x.1.isLt; omega⟩

/-- Suffix reindexing preserves chronological column order. -/
def suffixColumnEquiv {k d : ℕ} (x : Prefix k d) : Fin (d-x.1.val) ≃ tailColumns x where
  toFun j := ⟨suffixColumn x j,by simp [tailColumns,suffixColumn]⟩
  invFun j := ⟨j.val.val-x.1.val,by
    have hj := (Finset.mem_filter.mp j.property).2
    have := j.val.isLt
    omega⟩
  left_inv j := by apply Fin.ext; simp [suffixColumn]
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hj := (Finset.mem_filter.mp j.property).2
    dsimp [suffixColumn]
    omega

def inducedCuts {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n)) (x : Prefix k d)
    (ω₀ : Sample cuts) : Cuts k R.card (d-x.1.val) where
  count j a := (R.filter fun r => sampleEntry ω₀ r (suffixColumn x j)=a).card
  sum_count j := by
    simpa only [Finset.mem_univ,Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter R (Finset.univ : Finset (Fin k))
        (fun r => sampleEntry ω₀ r (suffixColumn x j))

theorem enumeration_card {k n : ℕ} (R : Finset (Fin n)) (q : R → Fin k) (a : Fin k) :
    (Finset.univ.filter fun i : Fin R.card => q (R.equivFin.symm i)=a).card=
      (Finset.univ.filter fun r : R => q r=a).card := by
  apply Finset.card_bij (fun i _ => R.equivFin.symm i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact R.equivFin.symm.injective hij
  · intro r hr
    refine ⟨R.equivFin r,?_,by simp⟩
    simpa using hr

def inducedColumnEquiv {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n)) (x : Prefix k d)
    (ω₀ : Sample cuts) (j : Fin (d-x.1.val)) :
    InteriorColumn R (ω₀ (suffixColumn x j)).val ≃ ColumnAssignments (inducedCuts cuts R x ω₀) j where
  toFun q := ⟨fun i => q.val (R.equivFin.symm i),fun a => (enumeration_card R q.val a).trans (q.property a)⟩
  invFun c := ⟨fun r => c.val (R.equivFin r),by
    intro a
    have he := enumeration_card R (fun r => c.val (R.equivFin r)) a
    simp only [Equiv.apply_symm_apply] at he
    exact he.symm.trans (c.property a)⟩
  left_inv q := by
    apply Subtype.ext
    funext r
    simp
  right_inv c := by
    apply Subtype.ext
    funext r
    simp

def inducedMatrixEquiv {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n)) (x : Prefix k d)
    (ω₀ : Sample cuts) : InteriorMatrix R (tailColumns x) ω₀ ≃ Sample (inducedCuts cuts R x ω₀) where
  toFun q := fun j => inducedColumnEquiv cuts R x ω₀ j (q (suffixColumnEquiv x j))
  invFun σ := fun j => ⟨fun r => (σ ((suffixColumnEquiv x).symm j)).val (R.equivFin r),by
    intro a
    let he := (inducedColumnEquiv cuts R x ω₀ ((suffixColumnEquiv x).symm j)).symm (σ ((suffixColumnEquiv x).symm j))
    have hp := he.property a
    have hj : suffixColumn x ((suffixColumnEquiv x).symm j)=j.val :=
      congrArg Subtype.val ((suffixColumnEquiv x).apply_symm_apply j)
    have hcEq := congrArg (fun t : Fin d => (R.filter fun r => (ω₀ t).val r=a).card) hj
    exact (show (Finset.univ.filter fun r : R => (σ ((suffixColumnEquiv x).symm j)).val (R.equivFin r)=a).card=
      (R.filter fun r => (ω₀ (suffixColumn x ((suffixColumnEquiv x).symm j))).val r=a).card from by
        simpa only [he,inducedColumnEquiv,Equiv.coe_fn_symm_mk] using hp).trans hcEq⟩
  left_inv q := by
    funext j
    apply Subtype.ext
    funext r
    simp only [inducedColumnEquiv,Equiv.coe_fn_mk,Equiv.symm_apply_apply]
    exact congrArg (fun j => (q j).val r) ((suffixColumnEquiv x).apply_symm_apply j)
  right_inv σ := by
    funext j
    apply Subtype.ext
    funext r
    simp only [inducedColumnEquiv,Equiv.coe_fn_mk,Equiv.apply_symm_apply]
    exact congrArg (fun j => (σ j).val r) ((suffixColumnEquiv x).symm_apply_apply j)

/-- The abstract induced-column product is exactly the existing concrete
fixed-count matrix model, with the original suffix column order. -/
theorem inducedMatrix_uniform {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n)) (x : Prefix k d)
    (ω₀ : Sample cuts) (f : Sample (inducedCuts cuts R x ω₀) → ℝ) :
    expect (PMF.uniformOfFintype (InteriorMatrix R (tailColumns x) ω₀))
      (fun q => f (inducedMatrixEquiv cuts R x ω₀ q))=
      expect (fixedCountPMF (inducedCuts cuts R x ω₀)) f :=
  RiffleLowerV2.Model.uniform_expect_equiv (inducedMatrixEquiv cuts R x ω₀) f

end RiffleUpperV2.Reservoir
