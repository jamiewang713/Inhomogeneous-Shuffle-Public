import RiffleUpperV2.FirstMoment.ClassFibers
import RiffleUpperV2.FirstMoment.StoppingCosts
import RiffleUpperV2.FirstMoment.MaximalCosts
import RiffleUpperV2.FirstMoment.TailCosts
import RiffleUpperV2.Localization.StableScales

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric

section ActualClasses
variable {k n d N : ℕ} (hk : 0 < k) (hN : 2 ≤ N)
    (cuts : Cuts k n (d+1)) (hn : 0 < n) (c : ColumnAssignments cuts 0)
    (T C chi delta width : ℝ) (hchi : 0 < chi) (hchi1 : chi ≤ 1)
    (hchiK : chi ≤ 1/(k : ℝ)) (hwidth : 0 < width) (hd : (d : ℝ) ≤ T*logScale N)
local notation "future" => tailCuts cuts
local notation "anchors" => (fun a : Fin k => anchorRows c a)
local notation "Candidate" => RetainedAtPile hk N future hn anchors C chi delta hchiK
local notation "default" => leftDefault hk future hn chi hchiK
local notation "join" => (fun t : Candidate => boundaryJoin t.2.1.1 t.2.1.2.1)
local notation "leaf" => (fun t : Candidate => t.2.1.2.2)
local notation "interval" => (fun t : Candidate => empiricalPositions d 0 (join t).1.val (leaf t).1.val)
local notation "classWords" => classPrefixes hk hN future hn anchors T C chi delta width hchi hchi1 hchiK hwidth hd
local notation "H" => (fun t : Candidate => Real.log ((classWords t).card : ℝ)/logScale N)
local notation "S" => (fun t : Candidate => goodCost N ((tailCuts cuts).profile hn) (interval t) chi (completePrefix default (leaf t)))
local notation "Q" => (fun t : Candidate => exceptionalCost N ((tailCuts cuts).profile hn) (interval t) chi (completePrefix default (leaf t)))
local notation "ell" => (fun t : Candidate => meanExponent N future (anchors t.1) (leaf t))
local notation "V" => (fun t : Candidate => meanExponent N future (anchors t.1) (join t))
local notation "F" => (fun t : Candidate => boundaryFluctuation N future (anchors t.1) (join t))
local notation "q" => crossingPenalty N chi

include hchi in
theorem retainedClass_genuine (s : Candidate) (hchiLt : chi < 1)
    (hnt : ¬TerminalBoundaryPair s.2.1.1 s.2.1.2.1) :
    GenuineBoundaryPair future (anchors s.1) chi s.2.1.1 s.2.1.2.1 (join s) :=
  genuine_of_nonterminal_boundaries hchi hchiLt s.2.2.1.1 s.2.2.1.2.1
    s.2.2.1.2.2.1 s.2.2.1.2.2.2.1 hnt

include hchi hN in
/-- The actual terminal margin removes every nonterminal-boundary fallback. -/
theorem retainedClass_stops (s : Candidate) (hchiLt : chi < 1)
    (a₀ : ℕ) {eta : ℝ} (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hgap : (q-eta)/2 < delta) (hnt : ¬TerminalBoundaryPair s.2.1.1 s.2.1.2.1) :
    Stops N future (anchors s.1) (join s) delta (leaf s) := by
  have hp := retainedClass_genuine hk cuts hn c C chi delta hchi hchiK s hchiLt hnt
  have hstable := s.2.2.1.2.2.2.2
  have hno := stable_no_fallback (by omega : 1<N) hn
    (anchoredFluctuationComparison N (by omega) future hn (anchors s.1) hp)
    (fun w hw hfull _ => firstPileTerminalExponent hN a₀ cuts hn c s.1 w hw hfull hmargin.1)
    hgap hstable
  by_contra hs
  exact hno ⟨hstable,hs⟩

/-- The actual descriptor entropy uses the original array's shifted interval. -/
theorem retainedClass_originalEntropy (hk2 : 2 ≤ k) (s : Candidate) (a₀ : ℕ)
    (theta : ℝ) (htheta : theta ∈ Set.Icc (3 : ℝ) 4) :
    H s ≤ theta*S s - empiricalB N a₀ cuts hn theta
      (a₀+1+(join s).1.val) (a₀+1+(leaf s).1.val) +
      (4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi) := by
  have h := retainedClassEntropy hk hN future hn anchors T C chi delta width
    hchi hchi1 hchiK hwidth hd hk2 s theta htheta
  rw [selectedPsi_eq_originalB cuts hn a₀ (join s).1.val (leaf s).1.val theta] at h
  exact h

/-- Large-route numerical exponent with all class, cost, maximum-word, stopping,
and fluctuation hypotheses discharged on the actual retained descriptor fiber. -/
theorem retainedClass_largeExponent (hk2 : 2 ≤ k) (s : Candidate) (hchiLt : chi < 1)
    (a₀ : ℕ) {eta : ℝ} (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hdelta : 0 ≤ delta) (hgap : (q-eta)/2 < delta)
    (hnt : ¬TerminalBoundaryPair s.2.1.1 s.2.1.2.1) :
    H s+4*ell s-F s-2*empiricalB N a₀ cuts hn 2 (a₀+1+(leaf s).1.val) (a₀+(d+1)) ≤
      -eta+delta+q/2+(4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi) := by
  have hp := retainedClass_genuine hk cuts hn c C chi delta hchi hchiK s hchiLt hnt
  have hx := s.2.2.1.2.2.2.2
  have hstop := retainedClass_stops hk hN cuts hn c C chi delta hchi hchiK s hchiLt a₀ hmargin hgap hnt
  have hq : 0 ≤ q := div_nonneg (Real.log_nonneg ((one_le_div hchi).mpr hchi1)) (logScale_pos hN).le
  have h := empiricalLargeExponent cuts hn (s := a₀+1+(join s).1.val)
    (u := a₀+1+(leaf s).1.val) hmargin (by omega)
    (Nat.add_le_add_left (prefix_length_le hx.2.1) (a₀+1)) (by have := (leaf s).1.isLt; omega)
    hdelta hq (anchoredExactCostSplit future hn (anchors s.1) default hx.2.1 hx.1 chi)
    (anchoredCosts_nonneg hN future hn (anchors s.1) default (join s) (leaf s) hx.1 chi).2
    (le_of_lt hstop) (anchoredFluctuationComparison N (by omega) future hn (anchors s.1) hp)
    (firstPileExponent_le_beta hN a₀ cuts hn c s.1 (join s) hp.legal_join)
    (retainedClass_originalEntropy hk hN cuts hn c T C chi delta width
      hchi hchi1 hchiK hwidth hd hk2 s a₀) (E := -empiricalB N a₀ cuts hn 2
      (a₀+1+(leaf s).1.val) (a₀+(d+1))) rfl
  convert h using 1 <;> ring

/-- Repaired small-proper numerical bound for literal retained classes. -/
theorem retainedClass_smallProperExponent (hk2 : 2 ≤ k) (s : Candidate) (hchiLt : chi < 1)
    (a₀ : ℕ) {eta : ℝ} (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hdelta : 0 ≤ delta) (hgap : (q-eta)/2 < delta)
    (hnt : ¬TerminalBoundaryPair s.2.1.1 s.2.1.2.1)
    (hproper : (join s).1.val < (leaf s).1.val) (hsmall : ell s ≤ 2*delta) :
    H s+4*ell s-2*empiricalB N a₀ cuts hn 2 (a₀+1+(leaf s).1.val) (a₀+(d+1)) ≤
      -eta+8*delta+21*q/2+(4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi) := by
  have hp := retainedClass_genuine hk cuts hn c C chi delta hchi hchiK s hchiLt hnt
  have hx := s.2.2.1.2.2.2.2
  have hstop := retainedClass_stops hk hN cuts hn c C chi delta hchi hchiK s hchiLt a₀ hmargin hgap hnt
  have hproper' : ProperStable N future (anchors s.1) (join s) delta (leaf s) := ⟨hx,hproper,hstop⟩
  have hq : 0 ≤ q := div_nonneg (Real.log_nonneg ((one_le_div hchi).mpr hchi1)) (logScale_pos hN).le
  have h := empiricalSmallExponent cuts hn (s := a₀+1+(join s).1.val)
    (u := a₀+1+(leaf s).1.val) hmargin (by omega)
    (Nat.add_le_add_left (prefix_length_le hx.2.1) (a₀+1)) (by have := (leaf s).1.isLt; omega) hq
    (anchoredCosts_nonneg hN future hn (anchors s.1) default (join s) (leaf s) hx.1 chi).1
    (properStable_goodCost hN future hn (anchors s.1) default (join s) (leaf s) delta chi
      hdelta hchi hchi1 hproper')
    (anchoredFluctuationComparison N (by omega) future hn (anchors s.1) hp)
    (firstPileExponent_le_beta hN a₀ cuts hn c s.1 (join s) hp.legal_join) hsmall
    (retainedClass_originalEntropy hk hN cuts hn c T C chi delta width
      hchi hchi1 hchiK hwidth hd hk2 s a₀) (E := -empiricalB N a₀ cuts hn 2
      (a₀+1+(leaf s).1.val) (a₀+(d+1))) rfl
  convert h using 1 <;> ring

/-- Small immediate fibers use only the original terminal margin and their
proved singleton cardinality. -/
theorem retainedClass_smallImmediateExponent (s : Candidate) (a₀ : ℕ) {eta : ℝ}
    (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hroot : leaf s = join s) (hsmall : ell s ≤ 2*delta) :
    H s+4*ell s-2*empiricalB N a₀ cuts hn 2 (a₀+1+(leaf s).1.val) (a₀+(d+1)) ≤
      -2*eta+4*delta := by
  have hH : H s = 0 := by
    have hw := classPrefixes_singleton_of_immediate hk hN future hn anchors T C chi delta width
      hchi hchi1 hchiK hwidth hd s hroot
    change Real.log ((classWords s).card : ℝ)/logScale N = 0
    rw [hw]
    simp
  have hx := s.2.2.1.2.2.2.2.1
  have h := empiricalImmediateExponent hN a₀ cuts hn (s := a₀+1+(leaf s).1.val)
    (by omega) (by have := (leaf s).1.isLt; omega) hmargin.1
    (firstPileExponent_le_beta hN a₀ cuts hn c s.1 (leaf s) hx)
    (E := -empiricalB N a₀ cuts hn 2 (a₀+1+(leaf s).1.val) (a₀+(d+1))) rfl
  have hh := immediateSmallDensityExponent h hsmall
  rw [hH]
  convert hh using 1 <;> ring

include hN in
/-- Actual terminal-boundary words satisfy the original terminal exponent. -/
theorem retainedClass_terminalExponent (s : Candidate) (a₀ : ℕ) {eta : ℝ}
    (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (ht : TerminalBoundaryPair s.2.1.1 s.2.1.2.1) : ell s ≤ -eta := by
  have hf := terminalBlock_full ⟨s.2.1,s.2.2.1⟩ ht
  exact firstPileTerminalExponent hN a₀ cuts hn c s.1 (leaf s) s.2.2.1.2.2.2.2.1 hf hmargin.1

end ActualClasses
end RiffleUpperV2.FirstMoment
