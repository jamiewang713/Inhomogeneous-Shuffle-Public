import RiffleUpperV2.Reservoir.SingleCylinderLaw
import RiffleUpperV2.Reservoir.OtherCylinder

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

/-- Auxiliary information for the entire family. No independence across
its different cylinders is asserted or needed. -/
def futureFamilyView {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (i : ℕ) (s : Word k (L+1)) (x : I → Prefix k (L+1)) (ω : Sample cuts) :=
  (naturalHistory cuts p d i ω,(fun a => cylinderRecord (x a) ω),wordCount ω s)

theorem futureFamilyView_counts {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (i : ℕ) (s : Word k (L+1)) (x : I → Prefix k (L+1)) (a : I) (ω₀ ω : Sample cuts)
    (h : futureFamilyView cuts p d i s x ω=futureFamilyView cuts p d i s x ω₀) :
    interiorCountsEq (cylinderRows (x a) ω₀) (tailColumns (x a)) ω₀ ω := by
  have hrec := congrArg (fun z => z.2.1 a) h
  have hR : cylinderRows (x a) ω=cylinderRows (x a) ω₀ := congrArg Prod.fst hrec
  intro j _ b
  have hc := congrArg (fun z => z.2.2.2 j b) hrec
  dsimp only [futureFamilyView,cylinderRecord] at hc
  rwa [hR] at hc

theorem futureFamilyView_interior_forward {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList → pileWords cuts p ω₀ j<w)
    (ω σ : Sample cuts)
    (h : futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
      futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀)
    (hf : interiorMatrixFiber (cylinderRows (x a) ω₀) (tailColumns (x a)) ω σ) :
    futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x σ=
      futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀ := by
  have hR : cylinderRows (x a) ω=cylinderRows (x a) ω₀ := congrArg (fun z => (z.2.1 a).1) h
  rw [← hR] at hf
  have hh := interior_history_forward cuts p ω₀ j (x a) hfuture ω σ hf (congrArg Prod.fst h)
  have hr : (fun b => cylinderRecord (x b) σ)=(fun b => cylinderRecord (x b) ω) := by
    funext b
    by_cases hab : a=b
    · subst b
      exact interior_cylinderRecord_eq cuts (x a) ω σ hf
    · exact interior_other_record_eq cuts (x a) (x b) (hsep a b hab) ω σ hf
  exact Prod.ext hh.1 (Prod.ext (hr.trans (congrArg (fun z => z.2.1) h))
    (hh.2.trans (congrArg (fun z => z.2.2) h)))

/-- Exact conditional induced-column product law on any chosen cylinder,
after revealing the whole disjoint family and the natural forward history. -/
theorem futureCylinderConditionalExpect_forward {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList → pileWords cuts p ω₀ j<w)
    (f : Sample cuts → ℝ) (g : InteriorMatrix (cylinderRows (x a) ω₀) (tailColumns (x a)) ω₀ → ℝ)
    (hf : ∀ ω (h : futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
      futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀),
      f ω=g (projectInterior _ _ ω₀ ω (futureFamilyView_counts cuts p .forward _ _ x a ω₀ ω h))) :
    conditionalExpect (fixedCountPMF cuts) f
      (fun ω => futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
        futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀)=
      expect (PMF.uniformOfFintype (InteriorMatrix (cylinderRows (x a) ω₀) (tailColumns (x a)) ω₀)) g := by
  exact interiorProjectionConditionalExpect cuts _ _ ω₀
    (fun ω => futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
      futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀) rfl
    (fun ω h => futureFamilyView_counts cuts p .forward _ _ x a ω₀ ω h)
    (futureFamilyView_interior_forward cuts p ω₀ j x hsep a hfuture) f g hf

theorem futureFamilyView_interior_backward {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList → w<backwardWords cuts p ω₀ j)
    (ω σ : Sample cuts)
    (h : futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
      futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀)
    (hf : interiorMatrixFiber (cylinderRows (x a) ω₀) (tailColumns (x a)) ω σ) :
    futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x σ=
      futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀ := by
  have hR : cylinderRows (x a) ω=cylinderRows (x a) ω₀ := congrArg (fun z => (z.2.1 a).1) h
  rw [← hR] at hf
  have hh := interior_history_backward cuts p ω₀ j (x a) hfuture ω σ hf (congrArg Prod.fst h)
  have hr : (fun b => cylinderRecord (x b) σ)=(fun b => cylinderRecord (x b) ω) := by
    funext b
    by_cases hab : a=b
    · subst b
      exact interior_cylinderRecord_eq cuts (x a) ω σ hf
    · exact interior_other_record_eq cuts (x a) (x b) (hsep a b hab) ω σ hf
  exact Prod.ext hh.1 (Prod.ext (hr.trans (congrArg (fun z => z.2.1) h))
    (hh.2.trans (congrArg (fun z => z.2.2) h)))

/-- Exact conditional induced-column product law on any chosen cylinder,
after revealing the whole disjoint family and the natural backward history. -/
theorem futureCylinderConditionalExpect_backward {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList → w<backwardWords cuts p ω₀ j)
    (f : Sample cuts → ℝ) (g : InteriorMatrix (cylinderRows (x a) ω₀) (tailColumns (x a)) ω₀ → ℝ)
    (hf : ∀ ω (h : futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
      futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀),
      f ω=g (projectInterior _ _ ω₀ ω (futureFamilyView_counts cuts p .backward _ _ x a ω₀ ω h))) :
    conditionalExpect (fixedCountPMF cuts) f
      (fun ω => futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
        futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀)=
      expect (PMF.uniformOfFintype (InteriorMatrix (cylinderRows (x a) ω₀) (tailColumns (x a)) ω₀)) g := by
  exact interiorProjectionConditionalExpect cuts _ _ ω₀
    (fun ω => futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
      futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀) rfl
    (fun ω h => futureFamilyView_counts cuts p .backward _ _ x a ω₀ ω h)
    (futureFamilyView_interior_backward cuts p ω₀ j x hsep a hfuture) f g hf

end RiffleUpperV2.Reservoir
