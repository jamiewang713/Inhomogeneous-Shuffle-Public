import RiffleUpperV2.Reservoir.InteriorMatrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile

def interiorCountsEq {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts) : Prop :=
  ∀ j∈J, ∀ a : Fin k, (R.filter fun r => sampleEntry ω r j=a).card=
    (R.filter fun r => sampleEntry ω₀ r j=a).card

def projectInterior {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts)
    (h : interiorCountsEq R J ω₀ ω) : InteriorMatrix R J ω₀ := fun j =>
  ⟨fun r => sampleEntry ω r.val j.val,fun a => (restriction_card R _ a).trans (h j.val j.property a)⟩

def fillInterior {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts)
    (h : interiorCountsEq R J ω₀ ω) (q : InteriorMatrix R J ω₀) : Sample cuts := fun j =>
  if hj : j∈J then patchColumn R (ω j)
    ⟨(q ⟨j,hj⟩).val,fun a => ((q ⟨j,hj⟩).property a).trans (h j hj a).symm⟩ else ω j

theorem fillInterior_outside {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts)
    (h : interiorCountsEq R J ω₀ ω) (q : InteriorMatrix R J ω₀) :
    interiorMatrixFiber R J ω (fillInterior R J ω₀ ω h q) := by
  intro j r hr
  dsimp only [fillInterior,sampleEntry]
  by_cases hj : j∈J
  · rw [dif_pos hj]
    exact patchValues_outside R (ω j).val _ r (hr.resolve_left (not_not.mpr hj))
  · rw [dif_neg hj]

theorem fillInterior_inside {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts)
    (h : interiorCountsEq R J ω₀ ω) (q : InteriorMatrix R J ω₀) (j : J) (r : R) :
    sampleEntry (fillInterior R J ω₀ ω h q) r.val j.val=(q j).val r := by
  dsimp only [fillInterior,sampleEntry]
  rw [dif_pos j.property]
  exact patchValues_inside R (ω j.val).val _ r

theorem fillInterior_counts {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts)
    (h : interiorCountsEq R J ω₀ ω) (q : InteriorMatrix R J ω₀) :
    interiorCountsEq R J ω₀ (fillInterior R J ω₀ ω h q) := by
  intro j hj a
  rw [← restriction_card]
  have he : (fun r : R => sampleEntry (fillInterior R J ω₀ ω h q) r.val j)=
      (q ⟨j,hj⟩).val := by
    funext r
    exact fillInterior_inside R J ω₀ ω h q ⟨j,hj⟩ r
  simp_rw [show ∀ r : R, sampleEntry (fillInterior R J ω₀ ω h q) r.val j=(q ⟨j,hj⟩).val r from fun r => congrFun he r]
  exact (q ⟨j,hj⟩).property a

theorem projectInterior_fill {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts)
    (h : interiorCountsEq R J ω₀ ω) (q : InteriorMatrix R J ω₀) :
    projectInterior R J ω₀ (fillInterior R J ω₀ ω h q) (fillInterior_counts R J ω₀ ω h q)=q := by
  funext j
  apply Subtype.ext
  funext r
  exact fillInterior_inside R J ω₀ ω h q j r

/-- Any concrete conditioning predicate which fixes the induced counts and
is invariant under every interior replacement has equal projection fibers.
The equivalences below replace the entire chosen rectangle explicitly. -/
def interiorProjectionFibers {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ : Sample cuts) (E : Sample cuts → Prop)
    (hc : ∀ ω, E ω → interiorCountsEq R J ω₀ ω)
    (hE : ∀ ω σ, E ω → interiorMatrixFiber R J ω σ → E σ)
    (a b : InteriorMatrix R J ω₀) :
    {ω : {ω : Sample cuts // E ω} // projectInterior R J ω₀ ω.val (hc ω.val ω.property)=a} ≃
    {ω : {ω : Sample cuts // E ω} // projectInterior R J ω₀ ω.val (hc ω.val ω.property)=b} where
  toFun ω := ⟨⟨fillInterior R J ω₀ ω.val.val (hc _ ω.val.property) b,
    hE _ _ ω.val.property (fillInterior_outside R J ω₀ _ _ b)⟩,
    projectInterior_fill R J ω₀ ω.val.val (hc ω.val.val ω.val.property) b⟩
  invFun ω := ⟨⟨fillInterior R J ω₀ ω.val.val (hc _ ω.val.property) a,
    hE _ _ ω.val.property (fillInterior_outside R J ω₀ _ _ a)⟩,
    projectInterior_fill R J ω₀ ω.val.val (hc ω.val.val ω.val.property) a⟩
  left_inv ω := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    apply Subtype.ext
    funext r
    by_cases hj : j∈J
    · by_cases hr : r∈R
      · have he := congrArg (fun q : InteriorMatrix R J ω₀ => (q ⟨j,hj⟩).val ⟨r,hr⟩) ω.property
        simpa only [fillInterior,dif_pos hj,patchColumn,patchValues,dif_pos hr,projectInterior,sampleEntry] using he.symm
      · simp only [fillInterior,dif_pos hj,patchColumn,patchValues,dif_neg hr]
    · simp only [fillInterior,dif_neg hj]
  right_inv ω := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    apply Subtype.ext
    funext r
    by_cases hj : j∈J
    · by_cases hr : r∈R
      · have he := congrArg (fun q : InteriorMatrix R J ω₀ => (q ⟨j,hj⟩).val ⟨r,hr⟩) ω.property
        simpa only [fillInterior,dif_pos hj,patchColumn,patchValues,dif_pos hr,projectInterior,sampleEntry] using he.symm
      · simp only [fillInterior,dif_pos hj,patchColumn,patchValues,dif_neg hr]
    · simp only [fillInterior,dif_neg hj]

theorem interiorProjectionConditionalExpect {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ : Sample cuts) (E : Sample cuts → Prop)
    (he : E ω₀) (hc : ∀ ω, E ω → interiorCountsEq R J ω₀ ω)
    (hE : ∀ ω σ, E ω → interiorMatrixFiber R J ω σ → E σ)
    (f : Sample cuts → ℝ) (g : InteriorMatrix R J ω₀ → ℝ)
    (hf : ∀ ω (h : E ω), f ω=g (projectInterior R J ω₀ ω (hc ω h))) :
    conditionalExpect (fixedCountPMF cuts) f E=
      expect (PMF.uniformOfFintype (InteriorMatrix R J ω₀)) g := by
  letI : Nonempty {ω : Sample cuts // E ω} := ⟨⟨ω₀,he⟩⟩
  exact conditionalUniformProjectionExpect E (fun ω => projectInterior R J ω₀ ω.val (hc ω.val ω.property))
    (interiorProjectionFibers cuts R J ω₀ E hc hE) f g hf

end RiffleUpperV2.Reservoir
