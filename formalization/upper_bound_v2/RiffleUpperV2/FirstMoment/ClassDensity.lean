import RiffleUpperV2.FirstMoment.ClassExponents
import RiffleUpperV2.FirstMoment.DensityPowers
import RiffleUpperV2.FirstMoment.FirstPileReserve

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

/-- Every actual small-proper retained fiber satisfies the finite class density
bound, with the exact entropy and crossing losses displayed. -/
theorem retainedClass_smallProperDensity (hk2 : 2 ≤ k) (s : Candidate) (hchiLt : chi < 1)
    (a₀ : ℕ) {eta : ℝ} (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hdelta : 0 ≤ delta) (hgap : (q-eta)/2 < delta)
    (hnt : ¬TerminalBoundaryPair s.2.1.1 s.2.1.2.1)
    (hproper : (join s).1.val < (leaf s).1.val) (hsmall : ell s ≤ 2*delta)
    (c₀ : ℤ) (slots : Finset ℤ) :
    ((classWords s).card : ℝ)*anchoredDensity future c₀ (anchors s.1) (leaf s) slots ≤
      (N : ℝ)^(-eta+8*delta+21*q/2+(4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi)) := by
  apply smallDensity_power hN future hn c₀ (anchors s.1) (leaf s) s.2.2.1.2.2.2.2.1
    slots (classWords s)
    ⟨leaf s,mem_classPrefixes hk hN future hn anchors T C chi delta width
      hchi hchi1 hchiK hwidth hd s⟩ (a₀+1)
  rw [empiricalB_tailCuts cuts hn a₀ (a₀+1+(leaf s).1.val) (a₀+1+d) (by omega) 2]
  have h := retainedClass_smallProperExponent hk hN cuts hn c T C chi delta width
    hchi hchi1 hchiK hwidth hd hk2 s hchiLt a₀ hmargin hdelta hgap hnt hproper hsmall
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- The immediate small case has singleton entropy and needs only the terminal margin. -/
theorem retainedClass_smallImmediateDensity (s : Candidate) (a₀ : ℕ) {eta : ℝ}
    (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hroot : leaf s = join s) (hsmall : ell s ≤ 2*delta) (c₀ : ℤ) (slots : Finset ℤ) :
    ((classWords s).card : ℝ)*anchoredDensity future c₀ (anchors s.1) (leaf s) slots ≤
      (N : ℝ)^(-2*eta+4*delta) := by
  apply smallDensity_power hN future hn c₀ (anchors s.1) (leaf s) s.2.2.1.2.2.2.2.1
    slots (classWords s)
    ⟨leaf s,mem_classPrefixes hk hN future hn anchors T C chi delta width
      hchi hchi1 hchiK hwidth hd s⟩ (a₀+1)
  rw [empiricalB_tailCuts cuts hn a₀ (a₀+1+(leaf s).1.val) (a₀+1+d) (by omega) 2]
  have h := retainedClass_smallImmediateExponent hk hN cuts hn c T C chi delta width
    hchi hchi1 hchiK hwidth hd s a₀ hmargin hroot hsmall
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Terminal fibers are actual singletons and are controlled by their actual mean. -/
theorem retainedClass_terminalDensity (s : Candidate) (a₀ : ℕ) {eta : ℝ}
    (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (ht : TerminalBoundaryPair s.2.1.1 s.2.1.2.1) (c₀ : ℤ) (slots : Finset ℤ) :
    ((classWords s).card : ℝ)*anchoredDensity future c₀ (anchors s.1) (leaf s) slots ≤
      (N : ℝ)^(-eta) := by
  have hw := classPrefixes_singleton_of_terminal hk hN future hn anchors T C chi delta width
    hchi hchi1 hchiK hwidth hd s ht
  change ((classWords s).card : ℝ)*_ ≤ _
  rw [hw,Finset.card_singleton,Nat.cast_one,one_mul]
  apply (terminalDensity future hn c₀ (anchors s.1) (leaf s) slots).trans
  rw [anchoredMean_rpow hN future (anchors s.1) (leaf s) s.2.2.1.2.2.2.2.1]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
  exact firstPileTerminalExponent hN a₀ cuts hn c s.1 (leaf s) s.2.2.1.2.2.2.2.1
    (terminalBlock_full ⟨s.2.1,s.2.2.1⟩ ht) hmargin.1

/-- Large actual descriptor fibers, with the first-column reserve proved from
FirstColumnGood and the smoothing failure kept visible. -/
theorem retainedClass_largeDensity (hk2 : 2 ≤ k) (s : Candidate) (hchiLt : chi < 1)
    (a₀ : ℕ) {eta g : ℝ} (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hg : 0 < g) (hg1 : g < 1) (hgood : FirstColumnGood cuts hn g)
    (hdelta : 0 ≤ delta) (hgap : (q-eta)/2 < delta)
    (hnt : ¬TerminalBoundaryPair s.2.1.1 s.2.1.2.1) (c₀ : ℤ) (slots : Finset ℤ) :
    ((classWords s).card : ℝ)*anchoredDensity future c₀ (anchors s.1) (leaf s) slots ≤
      4*Real.sqrt (varianceDenominator chi (join s)/g)*
        (N : ℝ)^(-eta+delta+q/2+(4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi)) +
      ((classWords s).card : ℝ)*(6*(slots.card : ℝ)*
        Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale future (anchors s.1) (join s))) := by
  have hp := retainedClass_genuine hk cuts hn c C chi delta hchi hchiK s hchiLt hnt
  have hd1 : 1 ≤ d := by
    have hyNot : s.2.1.1.1.val ≠ d := fun h => hnt (Or.inl h)
    have hyBound := s.2.1.1.1.isLt
    omega
  apply largeDensity_power hN future (firstColumnGood_population cuts hn hg hgood) hd1 c₀ (anchors s.1)
    (firstPileReserve cuts hn hg hg1 hgood c s.1) hp s.2.2.1.2.2.2.2.2.1
    s.2.2.1.2.2.2.2.1 slots (classWords s)
    ⟨leaf s,mem_classPrefixes hk hN future hn anchors T C chi delta width
      hchi hchi1 hchiK hwidth hd s⟩ (a₀+1)
  rw [empiricalB_tailCuts cuts hn a₀ (a₀+1+(leaf s).1.val) (a₀+1+d) (by omega) 2]
  have h := retainedClass_largeExponent hk hN cuts hn c T C chi delta width
    hchi hchi1 hchiK hwidth hd hk2 s hchiLt a₀ hmargin hdelta hgap hnt
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end ActualClasses
end RiffleUpperV2.FirstMoment
