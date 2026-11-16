import RiffleUpperV2.FirstMoment.RetainedGraphCover
import RiffleUpperV2.FirstMoment.ActiveClasses
import RiffleUpperV2.Shared.FirstMomentAPI

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric RiffleLowerV2.Thinning

/-- The existing first-moment law's marginal is the literal graph probability. -/
theorem edgeMarginal_eq_probability {k n d : ℕ} (cuts : Cuts k n d) (e : Fin (n-1)) :
    (toFirstMomentLaw cuts).edgeMarginal e =
      probability (fixedCountPMF cuts) (fun omega => e ∈ shuffleEdges omega) := by
  unfold InhomogeneousShuffle.FirstMoment.FiniteGraphLaw.edgeMarginal toFirstMomentLaw
    probability RiffleLowerV2.probability RiffleLowerV2.expect
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  by_cases h : e ∈ shuffleEdges omega <;> simp [h]

section GraphCover
variable {k n d N : ℕ} (hk : 0<k) (cuts : Cuts k n (d+1)) (hn : 0<n)
    (c : ColumnAssignments cuts 0) (C chi delta : ℝ) (hchiK : chi≤1/(k : ℝ))
local notation "future" => tailCuts cuts
local notation "R" => (fun a : Fin k => anchorRows c a)
local notation "offset" => firstPileStart cuts
local notation "Candidate" => RetainedAtPile hk N future hn R C chi delta hchiK

/-- Actual retained-block edge marginal in the common fixed-anchor law. -/
def retainedMarginal (t : Candidate) (m : ℤ) : ℝ :=
  anchoredEdgeProbability future (offset t.1) (R t.1) t.2.1.2.2 m

/-- Actual discarded-word edge probability, summed over the exposed piles. -/
def discardedMarginal (m : ℤ) : ℝ := ∑ p : Fin k,
  probability (fixedCountPMF future) (fun omega =>
    m ∈ edgesInWords (offset p) (R p)
      (vectorWords (discardedWords hk N future hn (R p) C chi delta hchiK)) omega)

/-- Actual global marginal cover after first-column exposure and relabeling. -/
theorem edgeMarginal_retained_cover (e : Fin (n-1)) :
    (toFirstMomentLaw cuts).edgeMarginal e ≤
      discardedMarginal (N := N) hk cuts hn c C chi delta hchiK e.val +
      ∑ t : Candidate, retainedMarginal hk cuts hn c C chi delta hchiK t e.val := by
  rw [edgeMarginal_eq_probability]
  have hglobal : probability (fixedCountPMF cuts) (fun omega => e ∈ shuffleEdges omega) ≤
      ∑ p : Fin k, probability (fixedCountPMF cuts)
        (fun omega => (e.val : ℤ) ∈ firstPileEdges p (emptyPrefix k d) omega) := by
    apply (probability_mono _ (fun omega he => (shuffleEdges_firstPile cuts omega e).mp he)).trans
    exact probability_iUnion_le _ _
  simp_rw [firstPileEdges_probability cuts c] at hglobal
  have hp := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) =>
    anchored_empty_probability_le (N := N) hk future hn R p C chi delta hchiK (offset p) e.val)
  have hs : (∑ p : Fin k, ∑ t : Candidate,
      if t.1=p then anchoredEdgeProbability future (offset p) (R p) t.2.1.2.2 e.val else 0) =
      ∑ t : Candidate, retainedMarginal hk cuts hn c C chi delta hchiK t e.val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp [retainedMarginal]
  rw [Finset.sum_add_distrib,hs] at hp
  exact hglobal.trans hp

/-- Every omitted retained block has marginal below the literal relevance threshold. -/
theorem retainedMarginal_le_of_inactive (t : Candidate) (m : ℤ) (epsilon : ℝ)
    (ht : t ∉ activeClasses hk cuts hn c C chi delta hchiK offset m epsilon) :
    retainedMarginal hk cuts hn c C chi delta hchiK t m ≤ epsilon := by
  have hnr : ¬Relevant future (offset t.1) (R t.1) m epsilon t.2.1.2.2 := by
    intro hr
    exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hr⟩)
  have hp : retainedMarginal hk cuts hn c C chi delta hchiK t m ≤
      probability (fixedCountPMF future) (fun omega => m ∈ anchoredInterval (offset t.1) (R t.1) t.2.1.2.2 omega) :=
    probability_mono _ (fun omega hm => anchoredEdges_subset_interval _ _ _ omega hm)
  exact hp.trans (le_of_lt (lt_of_not_ge hnr))

/-- The concrete localized marginal inequality used by the finite square-sum assembly. -/
theorem edgeMarginal_active_cover (e : Fin (n-1)) (epsilon : ℝ) (hepsilon : 0≤epsilon) :
    (toFirstMomentLaw cuts).edgeMarginal e ≤
      discardedMarginal (N := N) hk cuts hn c C chi delta hchiK e.val +
      (Fintype.card Candidate : ℝ)*epsilon +
      ∑ t ∈ activeClasses (N := N) hk cuts hn c C chi delta hchiK offset e.val epsilon,
        retainedMarginal hk cuts hn c C chi delta hchiK t e.val := by
  let A := activeClasses (N := N) hk cuts hn c C chi delta hchiK offset e.val epsilon
  let f := fun t : Candidate => retainedMarginal hk cuts hn c C chi delta hchiK t e.val
  have hs : (∑ t : Candidate, f t) ≤ (∑ t ∈ A, f t)+(Fintype.card Candidate : ℝ)*epsilon := by
    have hp : ∀ t : Candidate, f t ≤ (if t ∈ A then f t else 0)+epsilon := by
      intro t
      by_cases ht : t∈A
      · simp only [ht,if_true]
        linarith
      · simp only [ht,if_false,zero_add]
        exact retainedMarginal_le_of_inactive hk cuts hn c C chi delta hchiK t e.val epsilon ht
    have hh := Finset.sum_le_sum (fun t (_ : t∈Finset.univ) => hp t)
    have hi : (∑ t : Candidate, if t ∈ A then f t else 0) = ∑ t ∈ A, f t := by
      calc
        _ = ∑ t ∈ A, if t ∈ A then f t else 0 :=
          (Finset.sum_subset (Finset.subset_univ A) (by intro t _ ht; simp [ht])).symm
        _ = _ := Finset.sum_congr rfl (by intro t ht; simp [ht])
    simpa only [Finset.sum_add_distrib,hi,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh
  have h := edgeMarginal_retained_cover (N := N) hk cuts hn c C chi delta hchiK e
  change _ ≤ discardedMarginal (N := N) hk cuts hn c C chi delta hchiK e.val + _ + ∑ t∈A,f t
  linarith

end GraphCover
end RiffleUpperV2.FirstMoment
