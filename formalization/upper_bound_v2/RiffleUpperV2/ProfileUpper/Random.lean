import RiffleUpperV2.ProfileUpper.Mixture

noncomputable section
open Filter
namespace RiffleUpperV2.ProfileUpper
open TimeProfile

theorem randomEmpiricalBoundOfEmpirical (hE : Contracts.V1.E) :
    Contracts.V1.REmpiricalBound := by
  intro k hk T η g γ hT hη hg hγ
  obtain ⟨ρ0, hρ0, hρ⟩ := hE k hk T η g γ hT hη hg hγ
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ hρpos hρsmall
  obtain ⟨c, hc, N0, hN0, hEst⟩ := hρ ρ hρpos hρsmall
  refine ⟨c, hc, N0, hN0, ?_⟩
  intro N hN K hK Q
  let A := fun cuts : Cuts k N K => EmpiricalNegativeMargin N 0 cuts (by omega) η ∧
    LocalGood cuts (by omega) g γ ρ 0 ((K : ℝ)/Real.log (N : ℝ))
  have hb := mixtureBound Q physicalInverseLaw (uniformPermutation N) A
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-c)) (fun cuts h => hEst N hN K hK cuts h.1 h.2)
  have he := GraphOverlap.probability_compl Q A
  change RiffleLowerV2.probability Q (fun a => ¬ A a) = _ at he
  change tv (Q.bind physicalInverseLaw) (uniformPermutation N) ≤
    RiffleLowerV2.probability Q (fun a => ¬ A a) + _
  rw [he]
  exact hb

theorem randomEmpiricalOfEmpirical (hE : Contracts.V1.E) : Contracts.V1.REmpirical := by
  intro k hk T η g γ hT hη hg hγ
  obtain ⟨ρ0, hρ0, hρ⟩ := hE k hk T η g γ hT hη hg hγ
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ hρpos hρsmall K hK Q htyp
  obtain ⟨c, hc, N0, hN0, hEst⟩ := hρ ρ hρpos hρsmall
  apply mixtureTendsto Q (fun _ => physicalInverseLaw) (fun N => uniformPermutation N)
    (fun N cuts => ∃ hN : 2 ≤ N, EmpiricalNegativeMargin N 0 cuts (by omega) η ∧
      LocalGood cuts (by omega) g γ ρ 0 ((K N : ℝ)/Real.log (N : ℝ))) htyp
  intro δ hδ
  filter_upwards [eventually_ge_atTop N0,
    (powerDecay hc).eventually (eventually_lt_nhds hδ)] with N hN hdecay
  intro cuts hcuts
  obtain ⟨hN2, hm, hg⟩ := hcuts
  exact (hEst N hN (K N) (hK N hN2) cuts hm hg).trans hdecay.le

theorem randomProfileOfBuffered (hP : Contracts.V1.P) : Contracts.V1.RProfile := by
  intro k hk T η hT hη
  obtain ⟨χ0, hχ0, hχ⟩ := hP k hk T η hT hη
  refine ⟨χ0, hχ0, ?_⟩
  intro χ hχpos hχsmall P hPreg g γ hg hgk hγ
  obtain ⟨ρ0, hρ0, hρ⟩ := hχ χ hχpos hχsmall P hPreg g γ hg hgk hγ
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ hρpos hρsmall
  obtain ⟨φ0, hφ0, hφ⟩ := hρ ρ hρpos hρsmall
  refine ⟨φ0, hφ0, ?_⟩
  intro φ hφpos hφsmall μ hμ hm Q hLike hGood
  let A := fun N (cuts : Cuts k N (horizonDepth N T)) =>
    ∃ hN : 2 ≤ N, AlmostLike cuts (by omega) μ P T ρ φ
  let B := fun N (cuts : Cuts k N (horizonDepth N T)) =>
    ∃ hN : 2 ≤ N, LocalGood cuts (by omega) g γ ρ 0 T
  apply mixtureTendsto Q (fun _ => physicalInverseLaw) (fun N => uniformPermutation N)
    (fun N cuts => A N cuts ∧ B N cuts) (probabilityInterTendsto Q A B hLike hGood)
  intro δ hδ
  obtain ⟨N0, hN0, hEst⟩ := hφ φ hφpos hφsmall μ hμ hm δ hδ
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro cuts hcuts
  obtain ⟨⟨_, hl⟩, ⟨_, hg⟩⟩ := hcuts
  exact hEst N hN cuts hl hg

end RiffleUpperV2.ProfileUpper
