import RiffleUpperV2.FirstMoment.ClassExponents
import RiffleUpperV2.Localization.Eventual
import RiffleUpperV2.Shared.FiniteFiberCounts

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric

/-- A full first boundary forces the stable block to stop at its join. -/
theorem validBlock_terminal_immediate {k n d N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {chi delta : ℝ} {b : BlockTriple k d}
    (hb : ValidBlock N cuts R chi delta b) (ht : TerminalBoundaryPair b.1 b.2.1) :
    b.2.2 = boundaryJoin b.1 b.2.1 := by
  have hp := boundaryJoin_properties hb.2.2.1 hb.2.2.2.1
  have hfull : (boundaryJoin b.1 b.2.1).1.val=d := by
    have hbound := (boundaryJoin b.1 b.2.1).1.isLt
    rcases ht with hy | hz
    · have h := prefix_length_le hp.1
      omega
    · have h := prefix_length_le hp.2.1
      omega
  exact firstCut_eq_root (Or.inr hfull) hb.2.2.2.2.2

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

/-- Actual immediate blocks are retained at every edge; proper blocks are kept
precisely at the source relevance threshold. -/
def activeClasses (c₀ : Fin k → ℤ) (m : ℤ) (epsilon : ℝ) : Finset Candidate :=
  Finset.univ.filter (fun t => leaf t=join t ∨
    Relevant future (c₀ t.1) (anchors t.1) m epsilon (leaf t))

include hchi hN in
theorem retainedClass_proper_of_nonroot (s : Candidate) (hchiLt : chi < 1)
    (a₀ : ℕ) {eta : ℝ} (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hgap : (q-eta)/2 < delta) (hne : leaf s ≠ join s) :
    ProperStable N future (anchors s.1) (join s) delta (leaf s) := by
  have hx := s.2.2.1.2.2.2.2
  have hnt : ¬TerminalBoundaryPair s.2.1.1 s.2.1.2.1 := fun h =>
    hne (validBlock_terminal_immediate s.2.2.1 h)
  refine ⟨hx,?_,retainedClass_stops hk hN cuts hn c C chi delta hchi hchiK s hchiLt a₀ hmargin hgap hnt⟩
  apply lt_of_le_of_ne (prefix_length_le hx.2.1)
  intro he
  exact hne (prefix_eq_of_length hx.2.1 he).symm

/-- Each actual key contributes one immediate prefix or at most L relevant
proper prefixes, with no hidden boundary multiplicity. -/
theorem activeClasses_fiber_count (s : Candidate) (hchiLt : chi < 1)
    (a₀ : ℕ) {eta : ℝ} (hmargin : EmpiricalNegativeMargin N a₀ cuts hn eta)
    (hgap : (q-eta)/2 < delta) (c₀ : Fin k → ℤ) (m : ℤ) (epsilon : ℝ) (L : ℕ)
    (hrel : (relevantLeaves N future (c₀ s.1) (anchors s.1) (join s) delta m epsilon).card ≤ L) :
    ((activeClasses hk cuts hn c C chi delta hchiK c₀ m epsilon).filter (fun t =>
      retainedDescriptor hk hN future hn anchors T C chi delta width hchi hchi1 hchiK hwidth hd t =
      retainedDescriptor hk hN future hn anchors T C chi delta width hchi hchi1 hchiK hwidth hd s)).card ≤ L+1 := by
  classical
  let desc := retainedDescriptor hk hN future hn anchors T C chi delta width hchi hchi1 hchiK hwidth hd
  let A := (activeClasses hk cuts hn c C chi delta hchiK c₀ m epsilon).filter (fun t => desc t=desc s)
  have hinj : (A.image (fun t => leaf t)).card=A.card := by
    apply Finset.card_image_of_injOn
    intro t ht u hu he
    exact retainedDescriptor_prefix_injective hk hN future hn anchors T C chi delta width
      hchi hchi1 hchiK hwidth hd t u
      ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hu).2.symm) he
  change A.card ≤ L+1
  rw [← hinj]
  by_cases hroot : leaf s=join s
  · have hsub : A.image (fun t => leaf t) ⊆ classWords s := by
      intro x hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2⟩,rfl⟩
    have hb := Finset.card_le_card hsub
    rw [classPrefixes_singleton_of_immediate hk hN future hn anchors T C chi delta width
      hchi hchi1 hchiK hwidth hd s hroot,Finset.card_singleton] at hb
    omega
  · have hsproper := retainedClass_proper_of_nonroot hk hN cuts hn c C chi delta hchi hchiK
      s hchiLt a₀ hmargin hgap hroot
    have hsub : A.image (fun t => leaf t) ⊆
        relevantLeaves N future (c₀ s.1) (anchors s.1) (join s) delta m epsilon := by
      intro x hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      have he := (Finset.mem_filter.mp ht).2
      have hg := retainedDescriptor_eq_geometry hk hN future hn anchors T C chi delta width
        hchi hchi1 hchiK hwidth hd t s he
      have hnroot : leaf t ≠ join t := by
        intro hr
        have hlen : (leaf t).1.val=(join t).1.val := congrArg (fun x : Prefix k d => x.1.val) hr
        dsimp at hlen
        rw [hg.2.1,hg.2.2.1,hg.2.2.2] at hlen
        exact (ne_of_lt hsproper.2.1) hlen.symm
      have hproper := retainedClass_proper_of_nonroot hk hN cuts hn c C chi delta hchi hchiK
        t hchiLt a₀ hmargin hgap hnroot
      have ha := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
      have hrt : Relevant future (c₀ t.1) (anchors t.1) m epsilon (leaf t) := ha.resolve_left hnroot
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_⟩
      · simpa only [hg.1,hg.2.1,hg.2.2.1] using hproper
      · simpa only [hg.1] using hrt
    exact (Finset.card_le_card hsub).trans (hrel.trans (Nat.le_succ _))

end ActualClasses
end RiffleUpperV2.FirstMoment
