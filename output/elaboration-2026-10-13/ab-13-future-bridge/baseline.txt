import RiffleUpperV2.Reservoir.TailWords

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

def absoluteBlockGraph {k n d : ℕ} {cuts : Cuts k n d} (x : Prefix k d) (ω : Sample cuts) : Finset ℤ :=
  (blockGraph (cylinderRows x ω) ω).image (fun e => (lowerRank x ω:ℤ)+e.val)

def inducedGraphExpectation {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) (ω₀ : Sample cuts)
    (F : Finset ℤ → ℝ) : ℝ :=
  expect (fixedCountPMF (inducedCuts cuts (cylinderRows x ω₀) x ω₀))
    (fun σ => F ((shuffleEdges σ).image (fun e => (lowerRank x ω₀:ℤ)+e.val)))

/-- Exact graph-law transport, with absolute ranks and chronological tail columns,
for the actual forward history and complete family auxiliary information. -/
theorem futureCylinderGraphExpect_forward {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList → pileWords cuts p ω₀ j<w)
    (F : Finset ℤ → ℝ) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => F (absoluteBlockGraph (x a) ω))
      (fun ω => futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
        futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀)=
      inducedGraphExpectation cuts (x a) ω₀ F := by
  let R := cylinderRows (x a) ω₀
  let g : InteriorMatrix R (tailColumns (x a)) ω₀ → ℝ := fun q =>
    F ((shuffleEdges (inducedMatrixEquiv cuts R (x a) ω₀ q)).image (fun e => (lowerRank (x a) ω₀:ℤ)+e.val))
  have hh := futureCylinderConditionalExpect_forward cuts p ω₀ j x hsep a hfuture
    (fun ω => F (absoluteBlockGraph (x a) ω)) g (fun ω h => ?_)
  · apply hh.trans
    exact inducedMatrix_uniform cuts R (x a) ω₀
      (fun σ => F ((shuffleEdges σ).image (fun e => (lowerRank (x a) ω₀:ℤ)+e.val)))
  · have hR : cylinderRows (x a) ω=R := congrArg (fun z => (z.2.1 a).1) h
    have hlo : lowerRank (x a) ω=lowerRank (x a) ω₀ := congrArg (fun z => (z.2.1 a).2.1) h
    have hc := futureFamilyView_counts cuts p .forward _ _ x a ω₀ ω h
    have hp : ∀ r∈R, (rowWord ω r).toList.take (x a).1.val=(x a).2.toList := by
      intro r hr
      rw [← hR] at hr
      exact (Finset.mem_filter.mp hr).2
    unfold absoluteBlockGraph
    rw [hR,hlo,blockGraph_eq_induced cuts R (x a) ω₀ ω hc hp]

/-- Exact graph-law transport, with absolute ranks and chronological tail columns,
for the actual backward history and complete family auxiliary information. -/
theorem futureCylinderGraphExpect_backward {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList → w<backwardWords cuts p ω₀ j)
    (F : Finset ℤ → ℝ) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => F (absoluteBlockGraph (x a) ω))
      (fun ω => futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
        futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀)=
      inducedGraphExpectation cuts (x a) ω₀ F := by
  let R := cylinderRows (x a) ω₀
  let g : InteriorMatrix R (tailColumns (x a)) ω₀ → ℝ := fun q =>
    F ((shuffleEdges (inducedMatrixEquiv cuts R (x a) ω₀ q)).image (fun e => (lowerRank (x a) ω₀:ℤ)+e.val))
  have hh := futureCylinderConditionalExpect_backward cuts p ω₀ j x hsep a hfuture
    (fun ω => F (absoluteBlockGraph (x a) ω)) g (fun ω h => ?_)
  · apply hh.trans
    exact inducedMatrix_uniform cuts R (x a) ω₀
      (fun σ => F ((shuffleEdges σ).image (fun e => (lowerRank (x a) ω₀:ℤ)+e.val)))
  · have hR : cylinderRows (x a) ω=R := congrArg (fun z => (z.2.1 a).1) h
    have hlo : lowerRank (x a) ω=lowerRank (x a) ω₀ := congrArg (fun z => (z.2.1 a).2.1) h
    have hc := futureFamilyView_counts cuts p .backward _ _ x a ω₀ ω h
    have hp : ∀ r∈R, (rowWord ω r).toList.take (x a).1.val=(x a).2.toList := by
      intro r hr
      rw [← hR] at hr
      exact (Finset.mem_filter.mp hr).2
    unfold absoluteBlockGraph
    rw [hR,hlo,blockGraph_eq_induced cuts R (x a) ω₀ ω hc hp]

end RiffleUpperV2.Reservoir
