import RiffleUpperV2.FirstMoment.PowerAggregation
import RiffleUpperV2.Contracts.V1.Empirical

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric

/-- Uniform decay for the literal full graph with an exposed first column.
All thresholds precede the current population, absolute starting time, array,
and chosen first-column assignment. -/
theorem empiricalGraphDecay (k : ℕ) (hk : 2≤k) (T eta g : ℝ)
    (hT : 0<T) (heta : 0<eta) (hg : 0<g) (hgK : g<1/(k : ℝ)) :
    ∃ N0 : ℕ, 2≤N0 ∧ ∀ N n d : ℕ, N0≤N → ∀ hn : 0<n, n≤N →
      ∀ cuts : Cuts k n (d+1), ∀ a₀ : ℕ,
      (d : ℝ)≤T*logScale N → FirstColumnGood cuts hn g →
      EmpiricalNegativeMargin N a₀ cuts hn eta →
      expectedCommonEdges cuts≤(N : ℝ)^(-eta/8) := by
  let delta := eta/256
  let width := eta/256
  let epsilon := eta/64
  let D := eta+4
  let C := D+3
  have hdelta : 0<delta := by dsimp [delta]; positivity
  have hwidth : 0<width := hdelta
  have hepsilon : 0<epsilon := by dsimp [epsilon]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  have hCeq : D+3≤C := le_rfl
  obtain ⟨chi1,hchi1,hchi1K,hentropy⟩ := exists_small_chi hk hT.le (by positivity : 0<eta/64)
  obtain ⟨chi2,hchi2,hchi2K,hcount0⟩ := retainedClasses_uniform_count k T C epsilon hk hT.le hC hepsilon
  obtain ⟨chi3,hchi3,hchi3K,hdiscard⟩ := discardedRows_power_bound k T D C hk hT.le hD hCeq
  let chi := min chi1 (min chi2 chi3)/2
  have hmin : 0<min chi1 (min chi2 chi3) := lt_min hchi1 (lt_min hchi2 hchi3)
  have hchi : 0<chi := by dsimp [chi]; positivity
  have hchimin : chi<min chi1 (min chi2 chi3) := by dsimp [chi]; linarith
  have hc1 : chi<chi1 := hchimin.trans_le (min_le_left _ _)
  have hc2 : chi<chi2 := hchimin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hc3 : chi<chi3 := hchimin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hchiK : chi≤1/(k : ℝ) := hc1.le.trans hchi1K
  have hchiLt : chi<1 := hc2.trans (hchi2K.trans_le (min_le_left _ _))
  have hrare : 4*Real.log (k : ℝ)*exceptionalAllowance chi≤eta/256 := by
    have h := (hentropy chi hchi hc1).2
    linarith
  have hg1 : g<1 := hgK.trans_le (by
    apply (div_le_iff₀ (by exact_mod_cast (show 0<k by omega))).mpr
    norm_num
    exact_mod_cast (show 1≤k by omega))
  obtain ⟨N1,hN1,hcount⟩ := hcount0 chi hchi hc2 width hwidth
  obtain ⟨N2,hN2,hdensity⟩ := retainedClassDensity_eventually k hk T eta g C chi delta width
    hT.le heta hg hg1 hchi hchiLt hchiK hdelta le_rfl hwidth le_rfl hrare
  obtain ⟨N3,hN3,hactive⟩ := activeClasses_count_eventually k (by omega) T chi delta
    hT.le hchi hchiLt hchiK hdelta
  obtain ⟨N4,hN4,homitted⟩ := retainedOmitted_eventually k (by omega) T delta epsilon D hT.le hdelta
  obtain ⟨N5,hN5,hmulti⟩ := relevantMultiplicity_power_rate k T epsilon hT.le hepsilon
  obtain ⟨N6,hN6⟩ := exists_nat_ge (4*((k : ℝ)^2+1))
  obtain ⟨N7,hfinish⟩ := Filter.eventually_atTop.mp
    (InhomogeneousShuffle.FirstMoment.two_power_terms_eventually eta (eta/2-epsilon)
      (2*epsilon) 0 (eta/8) (by positivity) (by linarith)
      (by dsimp [epsilon]; linarith))
  refine ⟨N1+N2+N3+N4+N5+N6+N7+2,by omega,?_⟩
  intro N n d hNN hn hnN cuts a₀ hd hgood hmargin
  have hN : 2≤N := by omega
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNone : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  let c : ColumnAssignments cuts 0 := Classical.choice (inferInstance : Nonempty (ColumnAssignments cuts 0))
  let R := fun p : Fin k => anchorRows c p
  let future := tailCuts cuts
  let Candidate := RetainedAtPile (by omega) N future hn R C chi delta hchiK
  let classes := retainedClasses (by omega) hN future hn R T C chi delta width hchi hchiLt.le hchiK hwidth hd
  let L := classes.card*(2*k*d+1)
  let e := Real.exp (-(N : ℝ)^(delta/16))
  let z : ℝ := (Fintype.card Candidate : ℝ)*e
  have hc : (classes.card : ℝ)≤(N : ℝ)^epsilon :=
    hcount N n d (by omega) hN hn hd hchiLt.le hchiK future R delta
  have hL : (L : ℝ)≤(N : ℝ)^(2*epsilon) := by
    calc
      _ = (classes.card : ℝ)*((2*k*d+1 : ℕ) : ℝ) := by simp [L]
      _ ≤ (N : ℝ)^epsilon*(N : ℝ)^epsilon := mul_le_mul hc (hmulti N d (by omega) hd)
        (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hz : z≤(N : ℝ)^(-D) := homitted N n d (by omega) hN future hn R C chi width
    hchi hchiLt.le hchiK hwidth hd hc
  have hU : (∑ t : Candidate, anchoredDensity future (firstPileStart cuts t.1) (R t.1)
      t.2.1.2.2 (edgeSlots n))≤(N : ℝ)^(epsilon-eta/2) := by
    apply retainedDensity_sum_power (by omega) hN future hn R T C chi delta width
      hchi hchiLt.le hchiK hwidth hd (firstPileStart cuts) (edgeSlots n) epsilon eta hc
    intro t
    exact hdensity N n d (by omega) hN cuts hn c a₀ hmargin hgood hd t
      (firstPileStart cuts t.1) (edgeSlots n) (by simp; omega)
  have hact : ∀ m : Fin (n-1),
      (activeClasses (N := N) (by omega) cuts hn c C chi delta hchiK (firstPileStart cuts) m.val e).card≤L := by
    intro m
    exact hactive N n d (by omega) hN cuts hn c a₀ eta C width heta hmargin hwidth hd (firstPileStart cuts) m.val
  have hB : ∀ p : Fin k, expect (fixedCountPMF future) (fun omega =>
      ((FirstMoment.rowsInWords (R p) (discardedWords (by omega) N future hn (R p) C chi delta hchiK) omega).card : ℝ))≤
      (N : ℝ)^(-D) := fun p => hdiscard chi hchi hc3 hchiK N n d hN hn hnN hd future (R p) delta
  have hgraph := actualGraphAssembly (by omega) cuts hn c C chi delta hchiK e
    ((N : ℝ)^(-D)) ((N : ℝ)^(epsilon-eta/2)) (Real.exp_pos _).le L hact hB hU
  have herr : 4*(k : ℝ)^2*(N : ℝ)^(-D)+4*(n-1 : ℕ)*z^2≤(N : ℝ)^(-eta) := by
    apply graphError_power_bound hN hnN eta z heta (by dsimp [z,e]; positivity) hz
    exact hN6.trans (by exact_mod_cast (show N6≤N by omega))
  have hmain : 2*(L : ℝ)*(N : ℝ)^(epsilon-eta/2)≤2*(N : ℝ)^(3*epsilon-eta/2) := by
    calc
      _ ≤ 2*(N : ℝ)^(2*epsilon)*(N : ℝ)^(epsilon-eta/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by norm_num)) (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [mul_assoc,← Real.rpow_add hNp]; congr 2; ring
  have hbound : expectedCommonEdges cuts≤2*(N : ℝ)^(-eta)+2*(N : ℝ)^(3*epsilon-eta/2) := by
    have hpos := Real.rpow_nonneg hNp.le (-eta)
    change expectedCommonEdges cuts≤4*(k : ℝ)^2*(N : ℝ)^(-D)+4*(n-1 : ℕ)*z^2+
      2*(L : ℝ)*(N : ℝ)^(epsilon-eta/2) at hgraph
    linarith
  apply hbound.trans
  have hf := hfinish N (by omega)
  convert hf using 2 <;> congr 2 <;> ring

end RiffleUpperV2.FirstMoment
