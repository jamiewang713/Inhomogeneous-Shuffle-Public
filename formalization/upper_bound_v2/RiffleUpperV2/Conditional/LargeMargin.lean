import RiffleUpperV2.Conditional.LargeConcentration

noncomputable section
open Filter Topology
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open TimeProfile Anchor Exploration Reservoir RiffleUpperV2.Localization

/-- The observed cylinder size obeys the original-N logarithmic prefix bound. -/
theorem largeCylinder_sizeExponent {k N K : ℕ} (hk : 0<k) (hN : 2≤N)
    (cuts : Cuts k N K) (x : Prefix k K) (omega : Sample cuts)
    (hm : 0<(cylinderRows x omega).card) (hmu : 0<prefixMean cuts x)
    (hupper : ((cylinderRows x omega).card : ℝ)≤2*prefixMean cuts x) :
    Real.log ((cylinderRows x omega).card : ℝ)/Real.log (N : ℝ)≤
      1-empiricalA N 0 cuts (by omega) 0 x.1.val+Real.log 2/Real.log (N : ℝ) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmp : (0 : ℝ)<(cylinderRows x omega).card := by exact_mod_cast hm
  have hmean : anchoredMean cuts Finset.univ x=prefixMean cuts x := by
    simp [anchoredMean,prefixMean,RiffleLowerV2.prefixMean]
  have hlegal : Legal cuts Finset.univ x := by
    change 0<anchoredMean cuts Finset.univ x
    rwa [hmean]
  have hbeta := FirstMoment.anchoredExponent_le_beta hN 0 cuts (by omega) Finset.univ
    (fun _ => ⟨0,hk⟩) x hlegal
  simp only [meanExponent,hmean,empiricalBeta,zero_add] at hbeta
  have hlogne : Real.log (N : ℝ)≠0 := (logScale_pos hN).ne'
  rw [div_self hlogne] at hbeta
  have hlog := div_le_div_of_nonneg_right (Real.log_le_log hmp hupper) (logScale_pos hN).le
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hmu.ne',add_div] at hlog
  simp only [normalizedExponent,logScale] at hbeta hlog
  linarith

/-- The explicit coordinate and log-population errors eventually use at most
eta of margin, while preserving half the next-column goodness. -/
theorem largeCylinder_errors (k : ℕ) (T eta g xi : ℝ)
    (heta : 0<eta) (hg : 0<g) (hxi : 0<xi) :
    ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N →
      2*(N : ℝ)^(-xi/3)≤g/2 ∧
      (7/2 : ℝ)*(Real.log 2/Real.log (N : ℝ)+(k : ℝ)*T*(2*(N : ℝ)^(-xi/3)))+
        12*(k : ℝ)^4*T*(2*(N : ℝ)^(-xi/3))≤eta := by
  have hlog : Tendsto (fun N : ℕ=>Real.log 2/Real.log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hneg : Tendsto (fun N : ℕ=>2*(N : ℝ)^(-xi/3)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by positivity : 0<xi/3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
    simpa only [mul_zero,Function.comp_apply,neg_div] using h
  have herr := ((hlog.add (hneg.const_mul ((k : ℝ)*T))).const_mul (7/2 : ℝ)).add
    (hneg.const_mul (12*(k : ℝ)^4*T))
  norm_num only [mul_zero,zero_add] at herr
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp (hneg.eventually_le_const (by positivity : 0<g/2))
  obtain ⟨N2,hN2⟩ := eventually_atTop.mp (herr.eventually_le_const heta)
  refine ⟨N1+N2+2,by omega,?_⟩
  intro N hN
  exact ⟨hN1 N (by omega),hN2 N (by omega)⟩

/-- Actual H, original margin and next-column goodness imply the induced model
conditions. No derived size, profile closeness or margin premise remains. -/
theorem largeCylinder_preservation (k : ℕ) (hk : 2≤k) (T eta g : ℝ)
    (heta : 0<eta) (hg : 0<g) :
    ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N → ∀ hN : 2≤N,
      ∀ L : ℕ, ∀ cuts : Cuts k N (L+1), ∀ D : ℕ,
      ∀ x : Prefix k (L+1), ∀ omega : Sample cuts,
      ((L+1 : ℕ) : ℝ)≤T*logScale N →
      EmpiricalNegativeMargin N 0 cuts (by omega) (2*eta) →
      concentrationEvent cuts D g (eta/10) omega → (N : ℝ)^(eta/10)≤prefixMean cuts x →
      (∃ a : Fin (L+1), a.val=x.1.val ∧ GoodColumn (cuts.profile (by omega) a) g) →
      2≤(cylinderRows x omega).card ∧ (cylinderRows x omega).card≤N ∧
      ∀ hm : 0<(cylinderRows x omega).card,
        FirstColumnGood (inducedCuts cuts (cylinderRows x omega) x omega) hm (g/2) ∧
        EmpiricalNegativeMargin N x.1.val (inducedCuts cuts (cylinderRows x omega) x omega) hm eta := by
  obtain ⟨N1,hN1,hconc⟩ := largeCylinder_concentration (eta/10) (by positivity)
  obtain ⟨N2,hN2,herr⟩ := largeCylinder_errors k T eta g (eta/10) heta hg (by positivity)
  refine ⟨N1+N2,by omega,?_⟩
  intro N hNN hN L cuts D x omega hK hmargin hH hlarge hnext
  obtain ⟨hmlo,hmhi,hm2,hmN,hcoord⟩ := hconc N (by omega) k L cuts D g x omega hH hlarge
  refine ⟨hm2,hmN,?_⟩
  intro hm
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmu : 0<prefixMean cuts x := (Real.rpow_pos_of_pos hNp (eta/10)).trans_le hlarge
  obtain ⟨hgoodErr,hmarginErr⟩ := herr N (by omega)
  let q := inducedCuts cuts (cylinderRows x omega) x omega
  have hsize := largeCylinder_sizeExponent (by omega) hN cuts x omega hm hmu hmhi
  have hpq : ∀ j a, |prob (cuts.profile (by omega) (Margins.suffixIndex x.1.val j)) a-
      prob (q.profile hm j) a|≤2*(N : ℝ)^(-(eta/10)/3) := by
    intro j a
    have hc := hcoord hm j a
    rw [abs_sub_comm] at hc
    exact hc
  have hpres := Margins.inducedMargin hk hN cuts q hm (Nat.le_of_lt_succ x.1.isLt)
    (e := Real.log 2/Real.log (N : ℝ)) (ζ := 2*(N : ℝ)^(-(eta/10)/3))
    (by positivity) (by positivity) hK hmargin hsize hpq
  constructor
  · obtain ⟨a,ha,hgood⟩ := hnext
    have hlen : 0<L+1-x.1.val := by have := a.isLt; omega
    refine ⟨hlen,?_⟩
    have hj : suffixColumn x ⟨0,hlen⟩=a := by apply Fin.ext; simp [suffixColumn,ha]
    obtain ⟨b,c,hbc,hb,hc⟩ := hgood
    refine ⟨b,c,hbc,?_,?_⟩
    · have hh := hcoord hm ⟨0,hlen⟩ b
      rw [hj] at hh
      change g≤(cuts.count a b : ℝ)/N at hb
      exact le_trans (by linarith [(abs_le.mp hh).1]) le_rfl
    · have hh := hcoord hm ⟨0,hlen⟩ c
      rw [hj] at hh
      change g≤(cuts.count a c : ℝ)/N at hc
      exact le_trans (by linarith [(abs_le.mp hh).1]) le_rfl
  · exact Margins.negativeMargin_mono q hm (by linarith) hpres

end RiffleUpperV2.Conditional
