import RiffleUpperV2.FirstMoment.ActiveClasses

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric

theorem relevantLeaves_card_zero_of_full {k n d N : ℕ} (cuts : Cuts k n d)
    (c₀ : ℤ) (R : Finset (Fin n)) (v : Prefix k d) (delta : ℝ) (m : ℤ) (epsilon : ℝ)
    (hfull : v.1.val=d) : (relevantLeaves N cuts c₀ R v delta m epsilon).card=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro x _ h
  have hx := h.1.2.1
  have hb := x.1.isLt
  omega

/-- Uniform actual active multiplicity: at each edge every realized descriptor
contributes at most 2*k*d+1 blocks. The threshold precedes all array data. -/
theorem activeClasses_count_eventually (k : ℕ) (hk : 0<k) (T chi delta : ℝ)
    (hT : 0≤T) (hchi : 0<chi) (hchiLt : chi<1) (hchiK : chi≤1/(k : ℝ)) (hdelta : 0<delta) :
    ∃ N0 : ℕ, 2≤N0 ∧ ∀ N n d : ℕ, N0≤N → ∀ hN : 2≤N,
      ∀ (cuts : Cuts k n (d+1)) (hn : 0<n) (c : ColumnAssignments cuts 0)
        (a₀ : ℕ) (eta C width : ℝ), 0<eta →
      EmpiricalNegativeMargin N a₀ cuts hn eta → ∀ hwidth : 0<width,
      ∀ hd : (d : ℝ)≤T*logScale N, ∀ c₀ : Fin k → ℤ, ∀ m : ℤ,
      (activeClasses (N := N) hk cuts hn c C chi delta hchiK c₀ m (Real.exp (-(N : ℝ)^(delta/16)))).card ≤
        (retainedClasses hk hN (tailCuts cuts) hn (fun a => anchorRows c a) T C chi delta width
          hchi hchiLt.le hchiK hwidth hd).card*(2*k*d+1) := by
  obtain ⟨N1,hN1,hrel⟩ := relevantParents k hk T chi delta hT hchi hdelta
  obtain ⟨N2,hN2,hq⟩ := crossingPenalty_eventually chi delta hdelta
  refine ⟨max N1 N2,hN1.trans (le_max_left _ _),?_⟩
  intro N n d hN0 hN cuts hn c a₀ eta C width heta hmargin hwidth hd c₀ m
  have h1 : N1≤N := (le_max_left _ _).trans hN0
  have h2 : N2≤N := (le_max_right _ _).trans hN0
  have hgap : (crossingPenalty N chi-eta)/2<delta := by have := hq N h2; linarith
  let future := tailCuts cuts
  let R := fun a : Fin k => anchorRows c a
  let Candidate := RetainedAtPile hk N future hn R C chi delta hchiK
  let desc := retainedDescriptor hk hN future hn R T C chi delta width hchi hchiLt.le hchiK hwidth hd
  apply card_le_image_card_mul_of_fiber_bound desc
  intro key hkey
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hkey
  apply activeClasses_fiber_count hk hN cuts hn c T C chi delta width hchi hchiLt.le hchiK hwidth hd
    s hchiLt a₀ hmargin hgap c₀ m (Real.exp (-(N : ℝ)^(delta/16))) (2*k*d)
  by_cases ht : TerminalBoundaryPair s.2.1.1 s.2.1.2.1
  · have hroot := validBlock_terminal_immediate s.2.2.1 ht
    have hfull : (boundaryJoin s.2.1.1 s.2.1.2.1).1.val=d := by
      rw [← hroot]
      exact terminalBlock_full ⟨s.2.1,s.2.2.1⟩ ht
    rw [relevantLeaves_card_zero_of_full future (c₀ s.1) (R s.1) _ delta m _ hfull]
    exact Nat.zero_le _
  · exact hrel N n d h1 hd future hn (c₀ s.1) (R s.1) s.2.1.1 s.2.1.2.1 _
      (retainedClass_genuine hk cuts hn c C chi delta hchi hchiK s hchiLt ht) m

end RiffleUpperV2.FirstMoment
