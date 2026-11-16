import RiffleUpperV2.Reservoir.InteriorColumn

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile

/-- Outside a chosen rectangle the entire matrix is fixed. -/
def interiorMatrixFiber {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts) : Prop :=
  ∀ j r, j∉J ∨ r∉R → sampleEntry ω r j=sampleEntry ω₀ r j

def InteriorMatrix {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ : Sample cuts) :=
  (j : J) → InteriorColumn R (ω₀ j.val).val

instance {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ : Sample cuts) : Fintype (InteriorMatrix R J ω₀) := by
  unfold InteriorMatrix
  infer_instance

instance {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ : Sample cuts) : Nonempty (InteriorMatrix R J ω₀) :=
  ⟨fun j => interiorRestriction R (ω₀ j.val).val⟩

def interiorMatrixEquiv {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ : Sample cuts) :
    {ω : Sample cuts // interiorMatrixFiber R J ω₀ ω} ≃ InteriorMatrix R J ω₀ where
  toFun ω := fun j => interiorColumnEquiv R (ω₀ j.val)
    ⟨ω.val j.val,fun r hr => ω.property j.val r (Or.inr hr)⟩
  invFun q := ⟨fun j => if h : j∈J then patchColumn R (ω₀ j) (q ⟨j,h⟩) else ω₀ j,by
    intro j r h
    dsimp only [sampleEntry]
    by_cases hj : j∈J
    · rw [dif_pos hj]
      exact patchValues_outside R (ω₀ j).val (q ⟨j,hj⟩).val r (h.resolve_left (not_not.mpr hj))
    · rw [dif_neg hj]⟩
  left_inv ω := by
    apply Subtype.ext
    funext j
    by_cases hj : j∈J
    · dsimp only
      rw [dif_pos hj]
      change patchColumn R (ω₀ j) (interiorColumnEquiv R (ω₀ j)
        ⟨ω.val j,fun r hr => ω.property j r (Or.inr hr)⟩)=ω.val j
      exact congrArg Subtype.val ((interiorColumnEquiv R (ω₀ j)).symm_apply_apply
        ⟨ω.val j,fun r hr => ω.property j r (Or.inr hr)⟩)
    · apply Subtype.ext
      funext r
      simpa only [dif_neg hj,sampleEntry] using (ω.property j r (Or.inl hj)).symm
  right_inv q := by
    funext j
    apply Subtype.ext
    funext r
    dsimp only [interiorColumnEquiv,Equiv.coe_fn_mk]
    simp only [dif_pos j.property]
    exact patchValues_inside R (ω₀ j.val).val (q j).val r

/-- Conditional on the literal exterior of a rectangle, the entire interior
has the uniform product of its induced fixed-count column spaces. -/
theorem interiorMatrixConditionalExpect {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ : Sample cuts)
    (f : Sample cuts → ℝ) (g : InteriorMatrix R J ω₀ → ℝ)
    (hf : ∀ ω (h : interiorMatrixFiber R J ω₀ ω),
      f ω=g (interiorMatrixEquiv R J ω₀ ⟨ω,h⟩)) :
    conditionalExpect (fixedCountPMF cuts) f (interiorMatrixFiber R J ω₀)=
      expect (PMF.uniformOfFintype (InteriorMatrix R J ω₀)) g := by
  letI : Nonempty {ω : Sample cuts // interiorMatrixFiber R J ω₀ ω} := ⟨⟨ω₀,fun _ _ _ => rfl⟩⟩
  change RiffleLowerV2.conditionalExpect (PMF.uniformOfFintype (Sample cuts)) f _ = _
  rw [Anchor.uniform_conditional_expect_subtype]
  have he : (fun ω : {ω : Sample cuts // interiorMatrixFiber R J ω₀ ω} => f ω.val)=
      (fun ω => g (interiorMatrixEquiv R J ω₀ ω)) := by
    funext ω
    exact hf ω.val ω.property
  rw [he]
  exact RiffleLowerV2.Model.uniform_expect_equiv (interiorMatrixEquiv R J ω₀) g

end RiffleUpperV2.Reservoir
