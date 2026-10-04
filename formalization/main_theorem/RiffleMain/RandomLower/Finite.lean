import RiffleMain.RandomLower.CommonEvent

noncomputable section
set_option autoImplicit false
open scoped Topology
open RiffleLowerV2 TimeProfile Filter
open RiffleLowerV2.Targets
namespace RiffleMain.RandomLower

/-- Finite common-event lower bound for an arbitrary joint distribution of all columns. -/
theorem randomEmpiricalLower_finite (k : ℕ) (hk : 2 ≤ k) (T etaLargest etaCold : ℝ)
    (hT : 0 < T) (hl : 0 < etaLargest) (hc : 0 < etaCold)
    (chi gamma rho ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ (hN : 2 ≤ N)
      (Q : PMF (HorizonCuts k N T)),
      probability Q (fun cuts =>
        EmpiricalAlternative T cuts (deckPos hN) etaLargest etaCold chi gamma rho) -
        ε - commonNullError k N T etaLargest etaCold ≤
        tv (RiffleUpperV2.randomInverseLaw Q) (uniformPermutation N) := by
  obtain ⟨N0, hN0, hcommon⟩ := common_event k hk T etaLargest etaCold hT hl hc
    chi gamma rho ε hε
  refine ⟨N0, hN0, ?_⟩
  intro N hlarge hN Q
  obtain ⟨E, hsuccess, hnull⟩ := hcommon N hlarge hN
  exact mixture_tv_lower Q physicalInverseLaw (uniformPermutation N)
    (fun cuts => EmpiricalAlternative T cuts (deckPos hN)
      etaLargest etaCold chi gamma rho) E hε.le hsuccess hnull

end RiffleMain.RandomLower
