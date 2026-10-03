import RiffleUpperV2.Localization.EdgeMoments

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

def finiteOffsets {k n d : ℕ} (u : InternalHistory k n d) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (j.val : ℤ) ∈ internalOffsets u)

theorem finiteOffsets_card {k n d : ℕ} (u : InternalHistory k n d) :
    (finiteOffsets u).card = (internalOffsets u).card := by
  apply Finset.card_bij (fun j _ => (j.val : ℤ))
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro i _ j _ he
    exact Fin.ext (by exact_mod_cast he)
  · intro z hz
    obtain ⟨hl,hu⟩ := internalOffsets_bounds u hz
    have he : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hl
    have hn : z.toNat < n := by omega
    refine ⟨⟨z.toNat,hn⟩,?_,he⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [he] using hz⟩

theorem anchoredEdges_mem_iff {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) (m : ℤ) :
    m ∈ anchoredEdges c₀ R x ω ↔ ∃ j : Fin n,
      (j.val : ℤ) ∈ internalOffsets (internalHistory R x ω) ∧ lowerEndpoint c₀ R x ω+j.val = m := by
  constructor
  · intro hm
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
    obtain ⟨hl,hu⟩ := internalOffsets_bounds _ hj
    have hjnat : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hl
    have hjn : j.toNat < n := by omega
    refine ⟨⟨j.toNat,hjn⟩,?_,?_⟩
    · simpa only [hjnat] using hj
    · simpa only [hjnat] using he
  · rintro ⟨j,hj,he⟩
    exact Finset.mem_image.mpr ⟨j.val,hj,he⟩

theorem expectedOffsets_eq_sum {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) :
    expect (fixedCountPMF cuts) (fun ω => ((internalOffsets (internalHistory R x ω)).card : ℝ)) =
      ∑ j : Fin n, probability (fixedCountPMF cuts)
        (fun ω => (j.val : ℤ) ∈ internalOffsets (internalHistory R x ω)) := by
  have h := sum_edge_probabilities (fixedCountPMF cuts)
    (fun ω => finiteOffsets (internalHistory R x ω)) Finset.univ
  simp only [Finset.univ_inter, finiteOffsets_card] at h
  symm
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext ω
  simp [finiteOffsets]

/-- The atom premise is now discharged for the actual internal equal-word edge offsets. -/
theorem goodEdge_atom {k n d : ℕ} (cuts : Cuts k n d) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (hpair : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x)
    (m : ℤ) :
    let data := endpointSmoothing cuts (by omega) c₀ R hg hpair hvx
    probability (fixedCountPMF cuts) (fun ω => m ∈ anchoredEdges c₀ R x ω ∧ data.good ω) ≤
      (16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v))) *
        expect (fixedCountPMF cuts) (fun ω => ((internalOffsets (internalHistory R x ω)).card : ℝ)) := by
  let data := endpointSmoothing cuts (by omega) c₀ R hg hpair hvx
  change probability _ _ ≤ _
  have hm : probability (fixedCountPMF cuts) (fun ω => m ∈ anchoredEdges c₀ R x ω ∧ data.good ω) ≤
      probability (fixedCountPMF cuts) (fun ω => ∃ j : Fin n,
        lowerEndpoint c₀ R x ω+j.val=m ∧ data.good ω ∧ (j.val : ℤ) ∈ internalOffsets (internalHistory R x ω)) := by
    apply RiffleLowerV2.Thinning.probability_mono
    rintro ω ⟨he,hgood⟩
    obtain ⟨j,hj,heq⟩ := (anchoredEdges_mem_iff c₀ R x ω m).mp he
    exact ⟨j,heq,hgood,hj⟩
  calc
    _ ≤ _ := hm
    _ ≤ ∑ j : Fin n, probability (fixedCountPMF cuts) (fun ω =>
        lowerEndpoint c₀ R x ω+j.val=m ∧ data.good ω ∧ (j.val : ℤ) ∈ internalOffsets (internalHistory R x ω)) :=
      RiffleLowerV2.Thinning.probability_iUnion_le _ _
    _ ≤ ∑ j : Fin n, (16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v))) *
        probability (fixedCountPMF cuts) (fun ω => (j.val : ℤ) ∈ internalOffsets (internalHistory R x ω)) := by
      apply Finset.sum_le_sum
      intro j _
      exact (jointInternalOffsetAtoms cuts hn hd c₀ R hg hpair hvx
        (fun _ => j.val) (fun u => (j.val : ℤ) ∈ internalOffsets u) m).1
    _ = _ := by rw [← Finset.mul_sum, ← expectedOffsets_eq_sum]

end RiffleUpperV2.Localization
