import RiffleUpperV2.Hypergeometric.ConditionalAnchor
import RiffleUpperV2.Localization.EdgeRelabel

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Hypergeometric RiffleUpperV2.Localization RiffleLowerV2.Thinning

/-- The actual anchored rank set has the same law for every anchor set of the same size. -/
theorem anchoredEdges_expect_of_card_eq {k n d : ℕ} (cuts : Cuts k n d)
    (c₀ : ℤ) (R S : Finset (Fin n)) (hcard : R.card = S.card)
    (x : Prefix k d) (f : Finset ℤ → ℝ) :
    expect (fixedCountPMF cuts) (fun ω => f (anchoredEdges c₀ R x ω)) =
      expect (fixedCountPMF cuts) (fun ω => f (anchoredEdges c₀ S x ω)) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq R S hcard
  have h := RiffleLowerV2.Model.uniform_expect_equiv
    (RiffleLowerV2.Model.sampleRelabel cuts σ.symm)
    (fun ω => f (anchoredEdges c₀ S x ω))
  rw [← hσ] at h
  simp only [anchoredEdges_relabel] at h
  rw [hσ] at h
  exact h

@[simp] theorem anchorRows_card {k n d : ℕ} {cuts : Cuts k n (d+1)}
    (c : ColumnAssignments cuts 0) (a : Fin k) :
    (anchorRows c a).card = cuts.count 0 a := c.property a

/-- Exposing either actual first-column assignment gives the same future anchored graph law. -/
theorem firstColumnAnchoredLaw {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c c' : ColumnAssignments cuts 0) (a : Fin k) (c₀ : ℤ) (x : Prefix k d)
    (f : Finset ℤ → ℝ) :
    conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (anchoredEdges c₀ (anchorRows c a) x (tailSample ω)))
      (fun ω => ω 0 = c) =
    expect (fixedCountPMF (tailCuts cuts))
      (fun ω => f (anchoredEdges c₀ (anchorRows c' a) x ω)) := by
  exact (firstColumnConditionalExpect cuts c
    (fun ω => f (anchoredEdges c₀ (anchorRows c a) x ω))).trans
    (anchoredEdges_expect_of_card_eq _ _ _ _ (by simp) _ _)

/-- The zero-based beginning of the first-column pile, determined by the cut counts. -/
def firstPileStart {k n d : ℕ} (cuts : Cuts k n (d+1)) (a : Fin k) : ℤ :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin k => b < a), (cuts.count 0 b : ℤ)

/-- Anchored future edges with the actual exposed first-column row set. -/
def firstPileEdges {k n d : ℕ} {cuts : Cuts k n (d+1)} (a : Fin k)
    (x : Prefix k d) (ω : Sample cuts) : Finset ℤ :=
  anchoredEdges (firstPileStart cuts a) (anchorRows (ω 0) a) x (tailSample ω)

/-- Integrating the first column preserves the common anchored graph law.
The future cuts still have population n, irrespective of the size of the pile. -/
theorem firstPileEdges_expect {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) (a : Fin k) (x : Prefix k d)
    (f : Finset ℤ → ℝ) :
    expect (fixedCountPMF cuts) (fun ω => f (firstPileEdges a x ω)) =
      expect (fixedCountPMF (tailCuts cuts))
        (fun ω => f (anchoredEdges (firstPileStart cuts a) (anchorRows c a) x ω)) := by
  change expect (PMF.uniformOfFintype (Sample cuts)) _ = _
  have he := RiffleLowerV2.Thinning.uniform_expect_equiv
    (Fin.consEquiv (ColumnAssignments cuts)) (fun ω => f (firstPileEdges a x ω))
  refine he.symm.trans ?_
  rw [uniform_product_expect]
  have h (c' : ColumnAssignments cuts 0) :
      expect (fixedCountPMF (tailCuts cuts)) (fun ω =>
        f (firstPileEdges a x (Fin.cons c' ω))) =
      expect (fixedCountPMF (tailCuts cuts)) (fun ω =>
        f (anchoredEdges (firstPileStart cuts a) (anchorRows c a) x ω)) := by
    change expect (fixedCountPMF (tailCuts cuts))
      (fun ω => f (anchoredEdges (firstPileStart cuts a) (anchorRows c' a) x ω)) = _
    exact anchoredEdges_expect_of_card_eq _ _ _ _ (by simp) _ _
  change expect (PMF.uniformOfFintype (ColumnAssignments cuts 0))
    (fun c' => expect (fixedCountPMF (tailCuts cuts))
      (fun ω => f (firstPileEdges a x (Fin.cons c' ω)))) = _
  simp_rw [h]
  exact uniform_expect_const _

/-- In particular, each actual pile edge marginal equals the fixed-anchor marginal. -/
theorem firstPileEdges_probability {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) (a : Fin k) (x : Prefix k d) (m : ℤ) :
    probability (fixedCountPMF cuts) (fun ω => m ∈ firstPileEdges a x ω) =
      anchoredEdgeProbability (tailCuts cuts) (firstPileStart cuts a) (anchorRows c a) x m := by
  have h := firstPileEdges_expect cuts c a x (fun E => if m ∈ E then 1 else 0)
  unfold anchoredEdgeProbability probability RiffleLowerV2.probability
  convert h using 1 <;> congr 1 <;> funext ω <;> split_ifs <;> rfl

end RiffleUpperV2.FirstMoment
