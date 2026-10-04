import RiffleMain.RandomLower.Largest
import RiffleMain.RandomLower.Cold

noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
open RiffleLowerV2 TimeProfile Filter
open RiffleLowerV2.Targets RiffleLowerV2.EmpiricalLower
namespace RiffleMain.RandomLower

def runMargin (etaLargest etaCold : ℝ) : ℝ := min etaLargest (kappa0 etaCold)

theorem runMargin_pos {etaLargest etaCold : ℝ} (hl : 0 < etaLargest)
    (hc : 0 < etaCold) : 0 < runMargin etaLargest etaCold := by
  unfold runMargin kappa0 kappa
  positivity

theorem runMargin_le_one (etaLargest etaCold : ℝ) : runMargin etaLargest etaCold ≤ 1 := by
  have h := (min_le_right etaLargest (kappa0 etaCold)).trans
    (min_le_right (kappa etaCold/100) (1/1000 : ℝ))
  change runMargin etaLargest etaCold ≤ 1
  exact h.trans (by norm_num)

def commonNullError (k N : ℕ) (T etaLargest etaCold : ℝ) : ℝ :=
  largestRunError N (runMargin etaLargest etaCold) +
    ((N+1 : ℕ) : ℝ)^(k*horizonDepth N T)*coldNullError N etaCold

/-- One permutation event works simultaneously for every admissible cut array.
The event is chosen before any law on arrays is supplied. -/
theorem common_event (k : ℕ) (hk : 2 ≤ k) (T etaLargest etaCold : ℝ)
    (hT : 0 < T) (hl : 0 < etaLargest) (hc : 0 < etaCold)
    (chi gamma rho ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ hN : 2 ≤ N,
      ∃ E : Permutation N → Prop,
        (∀ cuts : HorizonCuts k N T,
          EmpiricalAlternative T cuts (deckPos hN) etaLargest etaCold chi gamma rho →
          1-ε ≤ probability (physicalInverseLaw cuts) E) ∧
        probability (uniformPermutation N) E ≤ commonNullError k N T etaLargest etaCold := by
  classical
  let b := runMargin etaLargest etaCold
  have hb : 0 < b := runMargin_pos hl hc
  obtain ⟨Nl, hNl, hrun⟩ := largest_common_event b ε hb hε
  obtain ⟨Nc, _, hcold⟩ := cold_event_all_parameters k hk T etaCold hT hc chi gamma rho ε hε
  obtain ⟨Nr, hr⟩ := eventually_atTop.mp
    (largestRunLength_eventually_admissible b hb (runMargin_le_one _ _))
  refine ⟨max Nl (max Nc Nr), hNl.trans (le_max_left _ _), ?_⟩
  intro N hlarge hN
  have hlN : Nl ≤ N := (le_max_left _ _).trans hlarge
  have hcN : Nc ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
  have hrN : Nr ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hlarge
  let C := fun cuts : HorizonCuts k N T => ColdAdmissible T hN cuts etaCold chi gamma rho
  have hchoose (cuts : HorizonCuts k N T) (hcuts : C cuts) := hcold N hcN hN cuts hcuts
  let A := fun cuts : HorizonCuts k N T =>
    if hcuts : C cuts then Classical.choose (hchoose cuts hcuts) else fun _ => False
  have hAsuccess (cuts : HorizonCuts k N T) (hcuts : C cuts) :
      1-ε ≤ probability (physicalInverseLaw cuts) (A cuts) := by
    dsimp only [A]
    rw [dif_pos hcuts]
    exact (Classical.choose_spec (hchoose cuts hcuts)).1
  have hAnull (cuts : HorizonCuts k N T) :
      probability (uniformPermutation N) (A cuts) ≤ coldNullError N etaCold := by
    dsimp only [A]
    split_ifs with hcuts
    · exact (Classical.choose_spec (hchoose cuts hcuts)).2
    · rw [Ascent.probability_false]
      unfold coldNullError
      positivity
  let R := fun π : Permutation N => HasIncreasingRun π (largestRunLength N b)
  let E := fun π : Permutation N => R π ∨ ∃ cuts : HorizonCuts k N T, A cuts π
  refine ⟨E, ?_, ?_⟩
  · intro cuts halt
    by_cases hbeta : b ≤ beta cuts (deckPos hN) (horizon N (horizonDepth N T))
    · have hs := hrun N hlN k (horizonDepth N T) cuts hN hbeta
      have hm := Ascent.probability_mono (physicalInverseLaw cuts)
        (fun π (hπ : R π) => (Or.inl hπ : E π))
      exact hs.trans hm
    · have hC : C cuts := by
        rcases halt with hlarge | ⟨hp, hg, hm⟩
        · exact (hbeta ((min_le_left _ _).trans hlarge)).elim
        · exact ⟨hp, hg, hm, (lt_of_not_ge hbeta).trans_le (min_le_right _ _)⟩
      have hs := hAsuccess cuts hC
      have hm := Ascent.probability_mono (physicalInverseLaw cuts)
        (fun π (hπ : A cuts π) => (Or.inr ⟨cuts, hπ⟩ : E π))
      exact hs.trans hm
  · have hR := probability_increasingRun_le (hr N hrN).2.1
    have hA := probability_exists_le_card_mul (uniformPermutation N) A hAnull
    have hcard : (Fintype.card (HorizonCuts k N T) : ℝ) ≤
        ((N+1 : ℕ) : ℝ)^(k*horizonDepth N T) := by
      exact_mod_cast card_cuts_le k N (horizonDepth N T)
    have hn : 0 ≤ coldNullError N etaCold := by unfold coldNullError; positivity
    have hA' := hA.trans (mul_le_mul_of_nonneg_right hcard hn)
    have hu := Ascent.probability_union_le (uniformPermutation N) R
      (fun π => ∃ cuts : HorizonCuts k N T, A cuts π)
    change probability (uniformPermutation N) E ≤ _ at hu
    change probability (uniformPermutation N) R ≤ largestRunError N b at hR
    exact hu.trans (add_le_add hR hA')

end RiffleMain.RandomLower
