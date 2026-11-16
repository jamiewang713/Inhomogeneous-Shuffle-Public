import RiffleUpperV2.FirstMoment.UniformGraph

noncomputable section
namespace RiffleUpperV2.FirstMoment
open TimeProfile

/-- The actual empirical first-moment theorem, with the exact frozen uniform
quantifiers and the original N logarithmic scale. -/
theorem empiricalFirstMoment : Contracts.V1.F := by
  intro k hk T eta g hT heta hg hgK
  obtain ⟨N0,hN0,hdecay⟩ := empiricalGraphDecay k hk T eta g hT heta hg hgK
  refine ⟨eta/8,by positivity,N0,hN0,?_⟩
  intro N hN n hn hnN a K haK hK
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K-a≠0)
  rw [hd]
  intro cuts hgood hmargin
  have hdK : d≤K := by omega
  have hdKr : (d : ℝ)≤K := by exact_mod_cast hdK
  have hh : (d : ℝ)≤T*logScale N := hdKr.trans hK
  simpa only [neg_div] using hdecay N n d hN (by omega) hnN cuts a hh hgood hmargin

end RiffleUpperV2.FirstMoment
