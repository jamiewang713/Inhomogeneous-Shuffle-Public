import RiffleMain.RandomLower.Finite
import RiffleMain.RandomLower.Numerical

noncomputable section
set_option autoImplicit false
open scoped Topology
open RiffleLowerV2 TimeProfile Filter
open RiffleLowerV2.Targets
namespace RiffleMain.RandomLower

/-- Random empirical lower endpoint, uniform in every joint law of the complete array.
This is the common-event assertion of the manuscript's randomized lower corollary. -/
theorem randomEmpiricalLower (k : ℕ) (hk : 2 ≤ k) (T etaLargest etaCold : ℝ)
    (hT : 0 < T) (hl : 0 < etaLargest) (hc : 0 < etaCold)
    (chi gamma rho ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ (hN : 2 ≤ N)
      (Q : PMF (HorizonCuts k N T)),
      probability Q (fun cuts =>
        EmpiricalAlternative T cuts (deckPos hN) etaLargest etaCold chi gamma rho) - ε ≤
        tv (RiffleUpperV2.randomInverseLaw Q) (uniformPermutation N) := by
  obtain ⟨Nf, hNf, hf⟩ := randomEmpiricalLower_finite k hk T etaLargest etaCold
    hT hl hc chi gamma rho (ε/2) (by positivity)
  obtain ⟨Ne, he⟩ := eventually_atTop.mp
    ((commonNullError_tendsto k T etaLargest etaCold hT hl hc).eventually
      (gt_mem_nhds (show 0 < ε/2 by positivity)))
  refine ⟨max Nf Ne, hNf.trans (le_max_left _ _), ?_⟩
  intro N hlarge hN Q
  have hfinite := hf N ((le_max_left _ _).trans hlarge) hN Q
  have herr := he N ((le_max_right _ _).trans hlarge)
  linarith

/-- Arbitrary dependence between random columns is retained in the asymptotic endpoint. -/
theorem randomEmpiricalLower_tendsto (k : ℕ) (hk : 2 ≤ k) (T etaLargest etaCold : ℝ)
    (hT : 0 < T) (hl : 0 < etaLargest) (hc : 0 < etaCold)
    (chi gamma rho : ℝ) (Q : ∀ N : ℕ, PMF (HorizonCuts k N T))
    (hgood : Tendsto (fun N => probability (Q N)
      (Admissible T etaLargest etaCold chi gamma rho N)) atTop (𝓝 1)) :
    Tendsto (fun N => tv (RiffleUpperV2.randomInverseLaw (Q N)) (uniformPermutation N))
      atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he : 0 < (1-a)/3 := by linarith
    obtain ⟨N0, hN0, hbound⟩ := randomEmpiricalLower k hk T etaLargest etaCold
      hT hl hc chi gamma rho ((1-a)/3) he
    have hp := hgood.eventually (lt_mem_nhds (show 1-(1-a)/3 < 1 by linarith))
    filter_upwards [eventually_ge_atTop N0, hp] with N hlarge hp
    have hN : 2 ≤ N := hN0.trans hlarge
    have ht := hbound N hlarge hN (Q N)
    have hid : Admissible (k := k) T etaLargest etaCold chi gamma rho N =
        (fun cuts => EmpiricalAlternative T cuts (deckPos hN)
          etaLargest etaCold chi gamma rho) := by
      funext cuts
      exact propext (admissible_iff T etaLargest etaCold chi gamma rho hN cuts)
    rw [hid] at hp
    linarith
  · intro a ha
    exact Eventually.of_forall fun N =>
      (Ascent.tv_le_one (RiffleUpperV2.randomInverseLaw (Q N)) (uniformPermutation N)).trans_lt ha

end RiffleMain.RandomLower
