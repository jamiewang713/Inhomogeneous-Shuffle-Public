import RiffleUpperV2.FirstMoment.ClassDensity
import RiffleUpperV2.FirstMoment.DensityRates

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric

/-- Uniform actual class-density decay. The threshold is selected before the
population, array, exposed assignment, descriptor, and edge-slot set. -/
theorem retainedClassDensity_eventually (k : ℕ) (hk : 2 ≤ k)
    (T eta g C chi delta width : ℝ) (hT : 0 ≤ T) (heta : 0 < eta)
    (hg : 0 < g) (hg1 : g < 1) (hchi : 0 < chi) (hchiLt : chi < 1)
    (hchiK : chi ≤ 1/(k : ℝ)) (hdelta : 0 < delta) (hdeltaSmall : delta ≤ eta/256)
    (hwidth : 0 < width) (hwidthSmall : width ≤ eta/256)
    (hrare : 4*Real.log (k : ℝ)*exceptionalAllowance chi ≤ eta/256) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N n d : ℕ, N0 ≤ N → ∀ hN : 2 ≤ N,
      ∀ (cuts : Cuts k n (d+1)) (hn : 0<n) (c : ColumnAssignments cuts 0) (a₀ : ℕ),
      EmpiricalNegativeMargin N a₀ cuts hn eta → FirstColumnGood cuts hn g →
      ∀ hd : (d : ℝ) ≤ T*logScale N,
      ∀ s : RetainedAtPile (by omega) N (tailCuts cuts) hn (fun a => anchorRows c a)
        C chi delta hchiK, ∀ c₀ : ℤ, ∀ slots : Finset ℤ, slots.card ≤ N →
      ((classPrefixes (by omega) hN (tailCuts cuts) hn (fun a => anchorRows c a)
        T C chi delta width hchi hchiLt.le hchiK hwidth hd s).card : ℝ)*
        anchoredDensity (tailCuts cuts) c₀ (anchorRows c s.1) s.2.1.2.2 slots ≤
          (N : ℝ)^(-eta/2) := by
  obtain ⟨N1,hN1,hq⟩ := crossingPenalty_eventually chi delta hdelta
  obtain ⟨N2,hN2,hpref⟩ := smoothingPrefactor_eventually T chi g (eta/16) hT hchi hg (by positivity)
  obtain ⟨N3,hN3,hfail⟩ := classFailure_eventually k (by omega) T g delta eta hT hg hdelta
  obtain ⟨N4,hN4,htwo⟩ := Compat.fixed_polynomial_le_rpow 2 T 0 (3*eta/16)
    (by norm_num) hT (by positivity)
  refine ⟨max N1 (max N2 (max N3 N4)),hN1.trans (le_max_left _ _),?_⟩
  intro N n d hN0 hN cuts hn c a₀ hmargin hgood hd s c₀ slots hslots
  have h1 : N1≤N := (le_max_left _ _).trans hN0
  have h2 : N2≤N := (le_max_left _ _).trans ((le_max_right _ _).trans hN0)
  have h3 : N3≤N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN0))
  have h4 : N4≤N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN0))
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNone : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hq' := hq N h1
  have hgap : (crossingPenalty N chi-eta)/2 < delta := by linarith
  have hlargeLoss : -eta+delta+crossingPenalty N chi/2+
      (4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi) ≤ -3*eta/4 := by linarith
  have hsmallLoss : -eta+8*delta+21*crossingPenalty N chi/2+
      (4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi) ≤ -3*eta/4 := by linarith
  let future := tailCuts cuts
  let R := fun a : Fin k => anchorRows c a
  let v := boundaryJoin s.2.1.1 s.2.1.2.1
  let x := s.2.1.2.2
  let W := classPrefixes (by omega) hN future hn R T C chi delta width hchi hchiLt.le hchiK hwidth hd s
  change (W.card : ℝ)*anchoredDensity future c₀ (R s.1) x slots ≤ _
  by_cases hterminal : TerminalBoundaryPair s.2.1.1 s.2.1.2.1
  · exact (retainedClass_terminalDensity (by omega) hN cuts hn c T C chi delta width
      hchi hchiLt.le hchiK hwidth hd s a₀ hmargin hterminal c₀ slots).trans
      (Real.rpow_le_rpow_of_exponent_le hNone (by linarith))
  · by_cases hlarge : 2*delta ≤ meanExponent N future (R s.1) x
    · have hden := retainedClass_largeDensity (by omega) hN cuts hn c T C chi delta width
        hchi hchiLt.le hchiK hwidth hd hk s hchiLt a₀ hmargin hg hg1 hgood hdelta.le hgap
        hterminal c₀ slots
      have hpair := retainedClass_genuine (by omega) cuts hn c C chi delta hchi hchiK s hchiLt hterminal
      have hstop := retainedClass_stops (by omega) hN cuts hn c C chi delta hchi hchiK s hchiLt a₀ hmargin hgap hterminal
      have hf := hfail N n d h3 hd future hn (R s.1) chi s.2.1.1 s.2.1.2.1 v x
        hpair hstop hlarge slots hslots W
      have hp := hpref N d h2 hd k v
      have hm : 4*Real.sqrt (varianceDenominator chi v/g)*
          (N : ℝ)^(-eta+delta+crossingPenalty N chi/2+
            (4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi)) ≤ (N : ℝ)^(-11*eta/16) := by
        calc
          _ ≤ (N : ℝ)^(eta/16)*(N : ℝ)^(-3*eta/4) :=
            mul_le_mul hp (Real.rpow_le_rpow_of_exponent_le hNone hlargeLoss)
              (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)
          _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
      have hs : (W.card : ℝ)*anchoredDensity future c₀ (R s.1) x slots ≤
          2*(N : ℝ)^(-11*eta/16) := by
        have hh := hden.trans (add_le_add hm hf)
        have he := Real.rpow_le_rpow_of_exponent_le hNone (by linarith : -eta ≤ -11*eta/16)
        linarith
      have htwo' := htwo N d h4 hd
      norm_num only [pow_zero,mul_one] at htwo'
      apply hs.trans
      calc
        _ ≤ (N : ℝ)^(3*eta/16)*(N : ℝ)^(-11*eta/16) :=
          mul_le_mul_of_nonneg_right htwo' (Real.rpow_nonneg hNp.le _)
        _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
    · have hsmall : meanExponent N future (R s.1) x ≤ 2*delta := le_of_lt (lt_of_not_ge hlarge)
      by_cases hroot : x=v
      · exact (retainedClass_smallImmediateDensity (by omega) hN cuts hn c T C chi delta width
          hchi hchiLt.le hchiK hwidth hd s a₀ hmargin hroot hsmall c₀ slots).trans
          (Real.rpow_le_rpow_of_exponent_le hNone (by linarith))
      · have hx := s.2.2.1.2.2.2.2
        have hproper : v.1.val < x.1.val := by
          apply lt_of_le_of_ne (prefix_length_le hx.2.1)
          intro he
          exact hroot (prefix_eq_of_length hx.2.1 he).symm
        exact (retainedClass_smallProperDensity (by omega) hN cuts hn c T C chi delta width
          hchi hchiLt.le hchiK hwidth hd hk s hchiLt a₀ hmargin hdelta.le hgap hterminal
          hproper hsmall c₀ slots).trans (Real.rpow_le_rpow_of_exponent_le hNone
            (hsmallLoss.trans (by linarith)))

end RiffleUpperV2.FirstMoment
