import RiffleLowerV2.EmpiricalLower.LargestAsymptotic
import RiffleLowerV2.EmpiricalLower.Cold

noncomputable section
namespace RiffleLowerV2.EmpiricalLower
open TimeProfile Targets

/-- The uniform empirical endpoint. All branch thresholds are chosen before N
and the cuts, so the same bound includes arrays alternating between the cases. -/
theorem empiricalCombined : Targets.EmpiricalCombinedTarget := by
  intro k hk T etaLargest etaCold hT hLargest hCold chi gamma rho ε hε
  obtain ⟨Nl, hNl, hlargest⟩ := largestOnly k hk T etaLargest hT hLargest ε hε
  by_cases hparams : ColdParameters k etaCold chi gamma rho
  · have hk0 : 0 < kappa0 etaCold := by unfold kappa0 kappa; positivity
    obtain ⟨Ns, _, hsplit⟩ := largestOnly k hk T (kappa0 etaCold) hT hk0 ε hε
    obtain ⟨Nc, _, hcold⟩ := coldOnly k hk T etaCold hT hCold chi gamma rho hparams ε hε
    refine ⟨max Nl (max Ns Nc), hNl.trans (le_max_left _ _), ?_⟩
    intro N hN hlarge cuts halt
    have hlN : Nl ≤ N := (le_max_left _ _).trans hlarge
    have hsN : Ns ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
    have hcN : Nc ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hlarge
    rcases halt with hl | ⟨_, hgood, hmargin⟩
    · exact hlargest N hN hlN cuts hl
    · by_cases hs : kappa0 etaCold ≤ beta cuts (deckPos hN) (horizon N (horizonDepth N T))
      · exact hsplit N hN hsN cuts hs
      · exact hcold N hN hcN cuts hgood hmargin (lt_of_not_ge hs)
  · refine ⟨Nl, hNl, ?_⟩
    intro N hN hlarge cuts halt
    rcases halt with hl | ⟨hp, _⟩
    · exact hlargest N hN hlarge cuts hl
    · exact (hparams hp).elim

end RiffleLowerV2.EmpiricalLower
