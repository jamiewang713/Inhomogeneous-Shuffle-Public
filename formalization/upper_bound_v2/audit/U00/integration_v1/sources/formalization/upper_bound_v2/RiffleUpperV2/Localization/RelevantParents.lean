import RiffleUpperV2.Localization.EndpointWindow
import RiffleUpperV2.Localization.IntervalInclusion
import RiffleUpperV2.Localization.Counting
import RiffleUpperV2.Localization.StableScales

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

def endpointError (d : ℕ) (B w : ℝ) : ℝ :=
  2*(d+1)*Real.exp (-w^2/(4*(d+1)^2*(B+w)))

def Relevant {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ) (R : Finset (Fin n))
    (m : ℤ) (ε : ℝ) (x : Prefix k d) : Prop :=
  ε ≤ probability (fixedCountPMF cuts) (fun ω => m ∈ anchoredInterval c₀ R x ω)

def relevantLeaves {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (c₀ : ℤ) (R : Finset (Fin n))
    (v : Prefix k d) (δ : ℝ) (m : ℤ) (ε : ℝ) : Finset (Prefix k d) :=
  Finset.univ.filter (fun x => ProperStable N cuts R v δ x ∧ Relevant cuts c₀ R m ε x)

/-- Relevance forces the parent mean interval enlarged by the actual endpoint window. -/
theorem relevant_parent_in_window {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (hn : 0 < n)
    (c₀ : ℤ) (R : Finset (Fin n)) {χ δ ε w : ℝ} {y z v x : Prefix k d} (m : ℤ)
    (hpair : GenuineBoundaryPair cuts R χ y z v) (hx : ProperStable N cuts R v δ x)
    (hrel : Relevant cuts c₀ R m ε x) (hw : 0 < w)
    (herr : endpointError d (χ⁻¹*sideScale cuts R v) w < ε) :
    meanLower cuts c₀ R (parent x)-w ≤ m ∧ (m : ℝ) ≤ meanUpper cuts c₀ R (parent x)+w := by
  have hvp := (proper_parent_not_stopped hx).1
  have hwindow := endpointWindow cuts hn c₀ R hpair hvp hw
  have hex : ∃ ω : Sample cuts, m ∈ anchoredInterval c₀ R x ω ∧
      max |(lowerEndpoint c₀ R (parent x) ω : ℝ)-meanLower cuts c₀ R (parent x)|
        |(upperEndpoint c₀ R (parent x) ω : ℝ)-meanUpper cuts c₀ R (parent x)| ≤ w := by
    by_contra hno
    have hsubset : ∀ ω : Sample cuts, m ∈ anchoredInterval c₀ R x ω →
        w < max |(lowerEndpoint c₀ R (parent x) ω : ℝ)-meanLower cuts c₀ R (parent x)|
          |(upperEndpoint c₀ R (parent x) ω : ℝ)-meanUpper cuts c₀ R (parent x)| := by
      intro ω hω
      exact lt_of_not_ge (fun h => hno ⟨ω,hω,h⟩)
    have hmono := RiffleLowerV2.Thinning.probability_mono (fixedCountPMF cuts) hsubset
    have hle : ε ≤ endpointError d (χ⁻¹*sideScale cuts R v) w := hrel.trans (hmono.trans hwindow)
    exact not_le_of_gt herr hle
  obtain ⟨ω,hω,hdev⟩ := hex
  have hp := anchoredInterval_subset c₀ R (takePrefix_isPrefix x (x.1.val-1) (Nat.sub_le _ _)) ω hω
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hp
  have hlo' : (lowerEndpoint c₀ R (parent x) ω : ℝ) ≤ m := by exact_mod_cast hlo
  have hhi' : (m : ℝ) ≤ (upperEndpoint c₀ R (parent x) ω : ℝ) := by exact_mod_cast hhi.le
  have hl := (abs_le.mp ((le_max_left _ _).trans hdev))
  have hu := (abs_le.mp ((le_max_right _ _).trans hdev))
  constructor <;> linarith

/-- Finite model-specific 2kd sparsity. Its only extra inputs are explicit scalar
window/error comparisons, supplied uniformly by the eventual scalar theorem. -/
theorem relevantParents_finite {k n d : ℕ} (N : ℕ) (hN : 1 < N) (hk : 0 < k)
    (cuts : Cuts k n d) (hn : 0 < n) (c₀ : ℤ) (R : Finset (Fin n))
    {χ δ ε w : ℝ} {y z v : Prefix k d} (m : ℤ)
    (hpair : GenuineBoundaryPair cuts R χ y z v) (hw : 0 < w)
    (herr : endpointError d (χ⁻¹*sideScale cuts R v) w < ε)
    (hgap : 2*w < (N : ℝ)^(boundaryFluctuation N cuts R v+δ)) :
    (relevantLeaves N cuts c₀ R v δ m ε).card ≤ 2*k*d := by
  let s := relevantLeaves N cuts c₀ R v δ m ε
  apply per_edge_multiplicity hk s
  · intro x hx
    have h := ((Finset.mem_filter.mp hx).2).1.2.1
    omega
  · intro j hj
    let ps := (s.image parent).filter (fun p => p.1.val=j)
    letI : LinearOrder (Prefix k d) := LinearOrder.lift' (fun x => x.2.toList)
      (fun _ _ h => prefix_ext h)
    apply enlargedIntervalMultiplicity ps (meanLower cuts c₀ R) (meanUpper cuts c₀ R) (m : ℝ) w
    · intro p hp q hq hpq
      have hpj := (Finset.mem_filter.mp hp).2
      have hqj := (Finset.mem_filter.mp hq).2
      exact mean_intervals_ordered cuts c₀ R (hpj.trans hqj.symm) hpq
    · intro p hp
      obtain ⟨x,hxs,hxp⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp).1
      have hx := ((Finset.mem_filter.mp hxs).2).1
      have hmean := proper_parent_mean hN hn hx
      rw [hxp] at hmean
      have hlength := expected_endpoint_length cuts hn c₀ R p
      change meanUpper cuts c₀ R p-meanLower cuts c₀ R p = _ at hlength
      rw [hlength]
      exact hgap.trans_le hmean
    · intro p hp
      obtain ⟨x,hxs,hxp⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp).1
      obtain ⟨hx,hrel⟩ := (Finset.mem_filter.mp hxs).2
      rw [← hxp]
      exact relevant_parent_in_window N cuts hn c₀ R m hpair hx hrel hw herr

end RiffleUpperV2.Localization
