import RiffleLowerV2.Ascent.Concentration
import RiffleLowerV2.Ascent.Expectation
import RiffleLowerV2.Ascent.Asymptotic
import RiffleLowerV2.Ascent.Mixture

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
namespace RiffleLowerV2.Ascent

theorem componentComparison : Targets.ComponentComparison :=
  componentComparison_of_concentration_expectation componentConcentration componentExpectation

theorem uniformGraphScan : Targets.UniformGraphScan :=
  uniformGraphScan_of_comparison componentComparison

/-- A graph-only event; the observable permutation test is the separate shared `scan`. -/
def graphScanSuccess {N : ℕ} (H0 : Finset ℤ) (δ : ℝ) (G : PathEdges N) : Prop :=
  ∃ q : Fin (N+1), (H0.card : ℝ)^(1/2+δ) ≤
    ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ)

/-- Uniform conditional Lalley test; only the explicitly displayed mixture identity is conditional. -/
theorem conditionalLalleyTest (a δ D ε : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ (H0 : Finset ℤ)
      (ρ : PMF (PathEdges N)) (P : PMF (Permutation N)),
      P = pathGraphMixture ρ →
      (N : ℝ)^a ≤ (H0.card : ℝ) →
      (∀ q : Fin (N+1), ((boundary (clipTranslate N H0 q.val)).card : ℝ) ≤
        D * Real.sqrt H0.card) →
      probability ρ (graphScanSuccess H0 δ)-ε ≤ tv P (uniformPermutation N) := by
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨n1, hn1⟩ := uniformGraphScan a δ D (ε/2) ha hδ hD hhalf
  obtain ⟨n2, hn2pos, hn2⟩ := uniform_null_scan_eventually uniformScan a δ (ε/2) ha hδ hhalf
  refine ⟨max n1 n2, hn2pos.trans (le_max_right _ _), ?_⟩
  intro N hN H0 ρ P hP hM hd
  have hgood (G : PathEdges N) (hg : graphScanSuccess H0 δ G) :
      1-ε/2 ≤ probability (uniformPermutation N) (fun π =>
        scan H0 ((H0.card : ℝ)^(1/2+δ/2)) (componentSort G π)) :=
    hn1 N ((le_max_left n1 n2).trans hN) H0 G hM hd hg
  have hnull := hn2 N ((le_max_right n1 n2).trans hN) H0 hM
  have h := graph_mixture_tv_lower ρ P hP (graphScanSuccess H0 δ)
    (scan H0 ((H0.card : ℝ)^(1/2+δ/2))) hhalf.le hgood hnull
  linarith

/-- Source `lem:lalley` for an explicit graph mixture, with every asymptotic input stated. -/
theorem conditionalLalleyTendsto (a δ D : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hD : 0 ≤ D)
    (H0 : ℕ → Finset ℤ) (ρ : (N : ℕ) → PMF (PathEdges N))
    (P : (N : ℕ) → PMF (Permutation N))
    (hP : ∀ N, P N = pathGraphMixture (ρ N))
    (hgeometry : ∀ᶠ N : ℕ in atTop, (N : ℝ)^a ≤ ((H0 N).card : ℝ) ∧
      ∀ q : Fin (N+1), ((boundary (clipTranslate N (H0 N) q.val)).card : ℝ) ≤
        D * Real.sqrt (H0 N).card)
    (hgood : Tendsto (fun N => probability (ρ N) (graphScanSuccess (H0 N) δ)) atTop (𝓝 1)) :
    Tendsto (fun N => tv (P N) (uniformPermutation N)) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    let ε := (1-x)/3
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨N0, _, hN0⟩ := conditionalLalleyTest a δ D ε ha hδ hD hε
    have hprob := hgood.eventually (lt_mem_nhds (show 1-ε < 1 by linarith))
    filter_upwards [eventually_ge_atTop N0, hgeometry, hprob] with N hN hgeom hp
    have ht := hN0 N hN (H0 N) (ρ N) (P N) (hP N) hgeom.1 hgeom.2
    dsimp [ε] at ht hp
    linarith
  · intro x hx
    exact Filter.Eventually.of_forall fun N => (tv_le_one (P N) (uniformPermutation N)).trans_lt hx

end RiffleLowerV2.Ascent
