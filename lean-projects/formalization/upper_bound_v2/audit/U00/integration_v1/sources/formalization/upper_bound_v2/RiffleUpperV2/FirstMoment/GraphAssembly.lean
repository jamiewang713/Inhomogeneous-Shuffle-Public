import RiffleUpperV2.FirstMoment.ErrorDensity
import RiffleUpperV2.FirstMoment.DensityAggregation

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric RiffleLowerV2.Thinning

/-- Finite assembly for the actual graph. All quantities are literal retained
block densities, active blocks, and discarded row expectations. -/
theorem actualGraphAssembly {k n d N : ℕ} (hk : 0<k)
    (cuts : Cuts k n (d+1)) (hn : 0<n) (c : ColumnAssignments cuts 0)
    (C chi delta : ℝ) (hchiK : chi≤1/(k : ℝ)) (epsilon B U : ℝ) (hepsilon : 0≤epsilon)
    (L : ℕ)
    (hactive : ∀ e : Fin (n-1),
      (activeClasses (N := N) hk cuts hn c C chi delta hchiK (firstPileStart cuts) e.val epsilon).card≤L)
    (hB : ∀ p : Fin k, expect (fixedCountPMF (tailCuts cuts)) (fun omega =>
      ((FirstMoment.rowsInWords (anchorRows c p)
        (discardedWords hk N (tailCuts cuts) hn (anchorRows c p) C chi delta hchiK) omega).card : ℝ))≤B)
    (hU : (∑ t : RetainedAtPile hk N (tailCuts cuts) hn (fun p=>anchorRows c p) C chi delta hchiK,
      anchoredDensity (tailCuts cuts) (firstPileStart cuts t.1) (anchorRows c t.1) t.2.1.2.2 (edgeSlots n))≤U) :
    expectedCommonEdges cuts ≤ 4*(k : ℝ)^2*B+
      4*(n-1 : ℕ)*((Fintype.card (RetainedAtPile hk N (tailCuts cuts) hn
        (fun p=>anchorRows c p) C chi delta hchiK) : ℝ)*epsilon)^2+2*(L : ℝ)*U := by
  let Candidate := RetainedAtPile hk N (tailCuts cuts) hn (fun p=>anchorRows c p) C chi delta hchiK
  let q := fun t : Candidate => fun e : Fin (n-1) =>
    retainedMarginal hk cuts hn c C chi delta hchiK t e.val
  let z : ℝ := (Fintype.card Candidate : ℝ)*epsilon
  let err := fun e : Fin (n-1) => discardedMarginal (N := N) hk cuts hn c C chi delta hchiK e.val+z
  let active := fun e : Fin (n-1) =>
    activeClasses (N := N) hk cuts hn c C chi delta hchiK (firstPileStart cuts) e.val epsilon
  have herr : ∀ e, 0≤err e := by
    intro e
    exact add_nonneg (discardedMarginal_bounds (N := N) hk cuts hn c C chi delta hchiK e.val).1
      (mul_nonneg (Nat.cast_nonneg _) hepsilon)
  have hq : ∀ t e, 0≤q t e := fun _ _=>probability_nonneg _ _
  have hloc : ∀ e, (toFirstMomentLaw cuts).edgeMarginal e≤err e+∑ t∈active e,q t e :=
    fun e=>edgeMarginal_active_cover hk cuts hn c C chi delta hchiK e epsilon hepsilon
  have hD := graphError_squares (N := N) hk cuts hn c C chi delta hchiK B z hB
  have hU' : ∀ _ : Unit, (∑ t∈Finset.univ.filter (fun _ : Candidate=>()=()),
      ∑ e : Fin (n-1),q t e^2)≤U := by
    intro _
    simpa [q,retainedMarginal,anchoredDensity_edgeSlots] using hU
  have h := InhomogeneousShuffle.FirstMoment.expectedCommonEdges_bound
    (toFirstMomentLaw cuts) (fun _ : Candidate=>()) active err q L
      (2*(k : ℝ)^2*B+2*(n-1 : ℕ)*z^2) U herr hq hactive hloc hD hU'
  rw [toFirstMomentLaw_expected] at h
  simpa only [Fintype.card_unit,Nat.cast_one,mul_one, z, Candidate] using
    (show expectedCommonEdges cuts ≤
      4*(k : ℝ)^2*B+4*(n-1 : ℕ)*z^2+2*(L : ℝ)*(Fintype.card Unit : ℝ)*U by
        nlinarith [h])

end RiffleUpperV2.FirstMoment
