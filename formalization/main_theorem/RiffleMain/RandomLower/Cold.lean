import RiffleMain.RandomLower.Basic
import RiffleLowerV2.EmpiricalLower.Cold

noncomputable section
set_option autoImplicit false
open scoped Topology
open RiffleLowerV2 TimeProfile Filter
open RiffleLowerV2.Targets RiffleLowerV2.EmpiricalLower
namespace RiffleMain.RandomLower

/-- The null exponent is exactly the exponent used in the manuscript's union test. -/
def coldNullExponent (eta : ℝ) : ℝ := (kappa eta/3)*(kappa eta/5)

theorem coldNullExponent_pos {eta : ℝ} (heta : 0 < eta) :
    0 < coldNullExponent eta := by unfold coldNullExponent kappa; positivity

theorem coldNullExponent_eq (eta : ℝ) :
    coldNullExponent eta = eta^2/15000000 := by unfold coldNullExponent kappa; ring

def coldNullError (N : ℕ) (eta : ℝ) : ℝ :=
  ((N : ℝ)+1)*Real.exp (-(N : ℝ)^(coldNullExponent eta))

def ColdAdmissible {k N : ℕ} (T : ℝ) (hN : 2 ≤ N) (cuts : HorizonCuts k N T)
    (eta chi gamma rho : ℝ) : Prop :=
  ColdParameters k eta chi gamma rho ∧
  LocalGood cuts (deckPos hN) chi gamma rho 0 T ∧
  eta ≤ lambda1 cuts (deckPos hN) ∧
  beta cuts (deckPos hN) (horizon N (horizonDepth N T)) < kappa0 eta

/-- A concrete cold-array event has uniform success and an explicit exponentially small
null probability. No witness or event is supplied as an assumption. -/
theorem cold_event (k : ℕ) (hk : 2 ≤ k) (T eta : ℝ) (hT : 0 < T) (heta : 0 < eta)
    (chi gamma rho : ℝ) (hparams : ColdParameters k eta chi gamma rho)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ (hN : 2 ≤ N)
      (cuts : HorizonCuts k N T),
      LocalGood cuts (deckPos hN) chi gamma rho 0 T →
      eta ≤ lambda1 cuts (deckPos hN) →
      beta cuts (deckPos hN) (horizon N (horizonDepth N T)) < kappa0 eta →
      ∃ A : Permutation N → Prop,
        1-ε ≤ probability (physicalInverseLaw cuts) A ∧
        probability (uniformPermutation N) A ≤ coldNullError N eta := by
  rcases hparams with ⟨hchi, hgamma, hrho, hbudget⟩
  have hhalf : 0 < ε/2 := by positivity
  have hkap : 0 < kappa eta := by unfold kappa; positivity
  obtain ⟨xi, hxi, _, P, _, hconstruct⟩ :=
    Localization.coldGeometryFromEmpirical k hk T eta rho chi gamma
      hT heta hrho hchi hgamma hbudget
  obtain ⟨Ng, hNg, hgeometry⟩ := hconstruct (ε/2) hhalf
  obtain ⟨Ne, _, hedges⟩ := manyEdges k hk T eta rho chi xi
    hT heta hrho hchi hxi P (ε/2) hhalf
  obtain ⟨Nt, htest⟩ := physical_scan_success (kappa eta/3) (kappa eta/5) 4 (ε/2)
    (by positivity) (by positivity) (by norm_num) hhalf
  refine ⟨max Ng (max Ne Nt), hNg.trans (le_max_left _ _), ?_⟩
  intro N hlarge hN cuts hgood hmargin hcold
  have hgN : Ng ≤ N := (le_max_left _ _).trans hlarge
  have heN : Ne ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
  have htN : Nt ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hlarge
  obtain ⟨W, G, hW, hG, _⟩ := hgeometry N hgN cuts (deckPos hN) hmargin hcold hgood
  let H0 := coldRelativeSet cuts (deckPos hN) P W G
  let A : Permutation N → Prop := scan H0 ((H0.card : ℝ)^(1/2+(kappa eta/5)/2))
  have hp := hedges N heN cuts (deckPos hN) W G hW hG
  have hp' := Ascent.probability_mono (fixedCountPMF cuts)
    (fun ω h => localized_edge_event_implies_scan cuts H0
      (prefixAt W.ms G.ambient) (kappa eta/5) ω h)
  rcases hG with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hM, _, hd, _⟩
  have hs := htest N htN k (horizonDepth N T) cuts H0 hM hd
  have hn := Ascent.uniform_null_scan_bound Ascent.uniformScan (deckPos hN) H0
    (by positivity : 0 < kappa eta/3) (by positivity : 0 < kappa eta/5) hM
  refine ⟨A, ?_, ?_⟩
  · change 1-ε ≤ probability (physicalInverseLaw cuts)
      (scan H0 ((H0.card : ℝ)^(1/2+(kappa eta/5)/2)))
    linarith
  · exact hn

/-- Invalid cold parameters simply make the cold set empty, as in the empirical endpoint. -/
theorem cold_event_all_parameters (k : ℕ) (hk : 2 ≤ k) (T eta : ℝ)
    (hT : 0 < T) (heta : 0 < eta) (chi gamma rho ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ (hN : 2 ≤ N)
      (cuts : HorizonCuts k N T),
      ColdAdmissible T hN cuts eta chi gamma rho →
      ∃ A : Permutation N → Prop,
        1-ε ≤ probability (physicalInverseLaw cuts) A ∧
        probability (uniformPermutation N) A ≤ coldNullError N eta := by
  by_cases hp : ColdParameters k eta chi gamma rho
  · obtain ⟨N0, hN0, hbound⟩ := cold_event k hk T eta hT heta chi gamma rho hp ε hε
    refine ⟨N0, hN0, ?_⟩
    intro N hlarge hN cuts hc
    exact hbound N hlarge hN cuts hc.2.1 hc.2.2.1 hc.2.2.2
  · refine ⟨2, le_rfl, ?_⟩
    intro N hlarge hN cuts hc
    exact (hp hc.1).elim

end RiffleMain.RandomLower
