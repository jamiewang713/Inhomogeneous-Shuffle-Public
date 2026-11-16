import RiffleUpperV2.Reservoir.InteriorCounts

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

/-- Actual auxiliary information for a cylinder: the natural history, labeled
row set, absolute rank interval, induced counts, and current multiplicity. -/
def futureCylinderView {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (i : ℕ) (s : Word k (L+1)) (x : Prefix k (L+1)) (ω : Sample cuts) :=
  (naturalHistory cuts p d i ω,cylinderRecord x ω,wordCount ω s)

theorem futureCylinderView_counts {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (i : ℕ) (s : Word k (L+1)) (x : Prefix k (L+1)) (ω₀ ω : Sample cuts)
    (h : futureCylinderView cuts p d i s x ω=futureCylinderView cuts p d i s x ω₀) :
    interiorCountsEq (cylinderRows x ω₀) (tailColumns x) ω₀ ω := by
  have hrec := congrArg (fun z => z.2.1) h
  have hR : cylinderRows x ω=cylinderRows x ω₀ := congrArg Prod.fst hrec
  intro j _ a
  have hc := congrArg (fun z => z.2.2.2 j a) hrec
  dsimp only [futureCylinderView,cylinderRecord] at hc
  rwa [hR] at hc

theorem futureCylinderView_interior_forward {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : Prefix k (L+1))
    (hfuture : ∀ w : Word k (L+1), w.toList.take x.1.val=x.2.toList → pileWords cuts p ω₀ j<w)
    (ω σ : Sample cuts)
    (h : futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
      futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀)
    (hf : interiorMatrixFiber (cylinderRows x ω₀) (tailColumns x) ω σ) :
    futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x σ=
      futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀ := by
  have hR : cylinderRows x ω=cylinderRows x ω₀ := congrArg (fun z => z.2.1.1) h
  rw [← hR] at hf
  have hh := interior_history_forward cuts p ω₀ j x hfuture ω σ hf (congrArg Prod.fst h)
  have hr := interior_cylinderRecord_eq cuts x ω σ hf
  exact Prod.ext hh.1 (Prod.ext (hr.trans (congrArg (fun z => z.2.1) h))
    (hh.2.trans (congrArg (fun z => z.2.2) h)))

theorem futureCylinderView_interior_backward {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : Prefix k (L+1))
    (hfuture : ∀ w : Word k (L+1), w.toList.take x.1.val=x.2.toList → w<backwardWords cuts p ω₀ j)
    (ω σ : Sample cuts)
    (h : futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
      futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀)
    (hf : interiorMatrixFiber (cylinderRows x ω₀) (tailColumns x) ω σ) :
    futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x σ=
      futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀ := by
  have hR : cylinderRows x ω=cylinderRows x ω₀ := congrArg (fun z => z.2.1.1) h
  rw [← hR] at hf
  have hh := interior_history_backward cuts p ω₀ j x hfuture ω σ hf (congrArg Prod.fst h)
  have hr := interior_cylinderRecord_eq cuts x ω σ hf
  exact Prod.ext hh.1 (Prod.ext (hr.trans (congrArg (fun z => z.2.1) h))
    (hh.2.trans (congrArg (fun z => z.2.2) h)))

/-- The actual fixed-count law inside a strict future cylinder, conditioned
on all the stated auxiliary data and the literal forward history. -/
theorem singleCylinderConditionalExpect_forward {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : Prefix k (L+1))
    (hfuture : ∀ w : Word k (L+1), w.toList.take x.1.val=x.2.toList → pileWords cuts p ω₀ j<w)
    (f : Sample cuts → ℝ) (g : InteriorMatrix (cylinderRows x ω₀) (tailColumns x) ω₀ → ℝ)
    (hf : ∀ ω (h : futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
      futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀),
      f ω=g (projectInterior _ _ ω₀ ω (futureCylinderView_counts cuts p .forward _ _ x ω₀ ω h))) :
    conditionalExpect (fixedCountPMF cuts) f
      (fun ω => futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
        futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀)=
      expect (PMF.uniformOfFintype (InteriorMatrix (cylinderRows x ω₀) (tailColumns x) ω₀)) g := by
  exact interiorProjectionConditionalExpect cuts _ _ ω₀
    (fun ω => futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
      futureCylinderView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀) rfl
    (fun ω h => futureCylinderView_counts cuts p .forward _ _ x ω₀ ω h)
    (futureCylinderView_interior_forward cuts p ω₀ j x hfuture) f g hf

theorem singleCylinderConditionalExpect_backward {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : Prefix k (L+1))
    (hfuture : ∀ w : Word k (L+1), w.toList.take x.1.val=x.2.toList → w<backwardWords cuts p ω₀ j)
    (f : Sample cuts → ℝ) (g : InteriorMatrix (cylinderRows x ω₀) (tailColumns x) ω₀ → ℝ)
    (hf : ∀ ω (h : futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
      futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀),
      f ω=g (projectInterior _ _ ω₀ ω (futureCylinderView_counts cuts p .backward _ _ x ω₀ ω h))) :
    conditionalExpect (fixedCountPMF cuts) f
      (fun ω => futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
        futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀)=
      expect (PMF.uniformOfFintype (InteriorMatrix (cylinderRows x ω₀) (tailColumns x) ω₀)) g := by
  exact interiorProjectionConditionalExpect cuts _ _ ω₀
    (fun ω => futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
      futureCylinderView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀) rfl
    (fun ω h => futureCylinderView_counts cuts p .backward _ _ x ω₀ ω h)
    (futureCylinderView_interior_backward cuts p ω₀ j x hfuture) f g hf

end RiffleUpperV2.Reservoir
