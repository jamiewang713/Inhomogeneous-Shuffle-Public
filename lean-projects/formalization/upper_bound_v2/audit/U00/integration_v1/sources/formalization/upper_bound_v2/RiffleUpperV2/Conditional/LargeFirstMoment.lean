import RiffleUpperV2.Conditional.LargeMargin

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.Conditional
open TimeProfile Exploration Reservoir

/-- The actual large-cylinder first moment. The threshold precedes all arrays,
prefixes, samples and concentration-event span parameters. All induced-model
conditions follow from the displayed source assumptions. -/
theorem largeCylinder_firstMoment (k : ℕ) (hk : 2≤k) (T eta g : ℝ)
    (hT : 0<T) (heta : 0<eta) (hg : 0<g) (hgK : g<1/(k : ℝ)) :
    ∃ N0 : ℕ, ∃ hN0 : 2≤N0, ∀ N : ℕ, ∀ hNN : N0≤N,
      ∀ L : ℕ, ∀ cuts : Cuts k N (L+1), ∀ D : ℕ,
      ∀ x : Prefix k (L+1), ∀ omega : Sample cuts,
      ((L+1 : ℕ) : ℝ)≤T*logScale N →
      EmpiricalNegativeMargin N 0 cuts (by omega) (2*eta) →
      concentrationEvent cuts D g (eta/10) omega → (N : ℝ)^(eta/10)≤prefixMean cuts x →
      (∃ a : Fin (L+1), a.val=x.1.val ∧ GoodColumn (cuts.profile (by omega) a) g) →
      expectedCommonEdges (inducedCuts cuts (cylinderRows x omega) x omega)≤(N : ℝ)^(-eta/8) := by
  obtain ⟨N1,hN1,hpres⟩ := largeCylinder_preservation k hk T eta g heta hg
  obtain ⟨N2,hN2,hfirst⟩ := FirstMoment.empiricalGraphDecay k hk T eta (g/2) hT heta
    (by positivity) (by linarith)
  refine ⟨N1+N2,by omega,?_⟩
  intro N hNN L cuts D x omega hK hmargin hH hlarge hnext
  have hN : 2≤N := by omega
  obtain ⟨hm2,hmN,hmodel⟩ := hpres N (by omega) hN L cuts D x omega hK hmargin hH hlarge hnext
  have hm : 0<(cylinderRows x omega).card := by omega
  obtain ⟨hgood,hinduced⟩ := hmodel hm
  obtain ⟨a,ha,hga⟩ := hnext
  have hlen : 0<L+1-x.1.val := by have := a.isLt; omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero hlen.ne'
  have hdK : d≤L+1 := by have := x.1.isLt; omega
  have hdKr : (d : ℝ)≤(L+1 : ℕ) := by exact_mod_cast hdK
  have hf : ∀ q : Cuts k (cylinderRows x omega).card (L+1-x.1.val),
      FirstColumnGood q hm (g/2) → EmpiricalNegativeMargin N x.1.val q hm eta →
      expectedCommonEdges q≤(N : ℝ)^(-eta/8) := by
    rw [hd]
    intro q hqgood hqmargin
    exact hfirst N (cylinderRows x omega).card d (by omega) hm hmN q x.1.val
      (hdKr.trans hK) hqgood hqmargin
  exact hf _ hgood hinduced

end RiffleUpperV2.Conditional
