import RiffleLowerV2.Model.Main
import RiffleLowerV2.Ascent.Main
import RiffleLowerV2.Localization.Edges

noncomputable section
namespace RiffleLowerV2.EmpiricalLower
open TimeProfile

/-- The actual graph is sampled from the canonical fixed-count column law. -/
def actualGraphLaw {k N K : ℕ} (cuts : Cuts k N K) : PMF (PathEdges N) :=
  (fixedCountPMF cuts).map shuffleEdges

/-- The independently proved physical law discharges the graph-mixture premise. -/
theorem physical_eq_actualGraphMixture {k N K : ℕ} (cuts : Cuts k N K) :
    physicalInverseLaw cuts = Ascent.pathGraphMixture (actualGraphLaw cuts) := by
  rw [Model.physical_graph_representation, Ascent.pathGraphMixture, actualGraphLaw,
    PMF.bind_map]
  rfl

theorem probability_actualGraphLaw {k N K : ℕ} (cuts : Cuts k N K)
    (A : PathEdges N → Prop) :
    probability (actualGraphLaw cuts) A =
      probability (fixedCountPMF cuts) (fun ω => A (shuffleEdges ω)) := by
  unfold probability actualGraphLaw
  exact Model.expect_map _ _ _

/-- The tested translate is selected from the graph alone in LB04. This actual-law
consequence has no representation or conditional scan-success premise. -/
theorem physical_scan_success (a δ D ε : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ k K : ℕ, ∀ (cuts : Cuts k N K)
      (H0 : Finset ℤ),
      (N : ℝ)^a ≤ (H0.card : ℝ) →
      (∀ q : Fin (N+1), ((boundary (clipTranslate N H0 q.val)).card : ℝ) ≤
        D * Real.sqrt H0.card) →
      probability (fixedCountPMF cuts) (fun ω =>
        Ascent.graphScanSuccess H0 δ (shuffleEdges ω)) - ε ≤
      probability (physicalInverseLaw cuts)
        (scan H0 ((H0.card : ℝ)^(1/2+δ/2))) := by
  obtain ⟨N0, hN0⟩ := Ascent.uniformGraphScan a δ D ε ha hδ hD hε
  refine ⟨N0, ?_⟩
  intro N hN k K cuts H0 hM hd
  have hgood (G : PathEdges N) (hg : Ascent.graphScanSuccess H0 δ G) :
      1-ε ≤ probability (uniformPermutation N) (fun π =>
        scan H0 ((H0.card : ℝ)^(1/2+δ/2)) (componentSort G π)) :=
    hN0 N hN H0 G hM hd hg
  have h := Ascent.graph_mixture_event_lower (actualGraphLaw cuts)
    (Ascent.graphScanSuccess H0 δ) (scan H0 ((H0.card : ℝ)^(1/2+δ/2))) hε.le hgood
  rwa [← physical_eq_actualGraphMixture, probability_actualGraphLaw] at h

/-- Source `lem:lalley`, uniformly specialized to the physical shuffle. The
remaining geometric and many-edge inputs are discharged in `coldOnly`. -/
theorem physical_lalley_test (a δ D ε : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ k K : ℕ, ∀ (cuts : Cuts k N K)
      (H0 : Finset ℤ),
      (N : ℝ)^a ≤ (H0.card : ℝ) →
      (∀ q : Fin (N+1), ((boundary (clipTranslate N H0 q.val)).card : ℝ) ≤
        D * Real.sqrt H0.card) →
      probability (fixedCountPMF cuts) (fun ω =>
        Ascent.graphScanSuccess H0 δ (shuffleEdges ω)) - ε ≤
      tv (physicalInverseLaw cuts) (uniformPermutation N) := by
  obtain ⟨N0, hN0, htest⟩ := Ascent.conditionalLalleyTest a δ D ε ha hδ hD hε
  refine ⟨N0, hN0, ?_⟩
  intro N hN k K cuts H0 hM hd
  have h := htest N hN H0 (actualGraphLaw cuts) (physicalInverseLaw cuts)
    (physical_eq_actualGraphMixture cuts) hM hd
  rwa [probability_actualGraphLaw] at h

/-- The ambient-prefix rank is an admissible translate, including deck endpoints. -/
theorem localized_edge_event_implies_scan {k N K : ℕ} (cuts : Cuts k N K)
    (H0 : Finset ℤ) (w : Prefix k K) (δ : ℝ) (ω : Sample cuts)
    (h : (H0.card : ℝ)^(1/2+δ) ≤
      ((shuffleEdges ω ∩ internalEdges (clipTranslate N H0
        (lowerRank w ω : ℤ))).card : ℝ)) :
    Ascent.graphScanSuccess H0 δ (shuffleEdges ω) := by
  have hq := Localization.prefix_rank_bounds ω w
  exact ⟨⟨lowerRank w ω, by omega⟩, h⟩

/-- The cold geometry discharges the scan size and boundary estimates with the
fixed exponents kappa/3 and kappa/5, uniformly over the varying data. -/
theorem coldGeometry_scan_test (k : ℕ) (eta ε : ℝ) (heta : 0 < eta)
    (hε : 0 < ε) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ K : ℕ, ∀ (cuts : Cuts k N K)
      (hN : 0 < N) (rho chi xi : ℝ) (P : BorelPartition k)
      (W : ColdWitnessData) (G : ColdGeometryData K P W),
      GeometrySpec cuts hN eta rho chi xi P W G →
      probability (fixedCountPMF cuts) (fun ω =>
        ((coldRelativeSet cuts hN P W G).card : ℝ)^(1/2+kappa eta/5) ≤
          ((shuffleEdges ω ∩ internalEdges (clipTranslate N
            (coldRelativeSet cuts hN P W G)
            (lowerRank (prefixAt W.ms G.ambient) ω : ℤ))).card : ℝ)) - ε ≤
        tv (physicalInverseLaw cuts) (uniformPermutation N) := by
  have hkap : 0 < kappa eta := by unfold kappa; positivity
  obtain ⟨N0, hN0, htest⟩ := physical_lalley_test (kappa eta/3)
    (kappa eta/5) 4 ε (by positivity) (by positivity) (by norm_num) hε
  refine ⟨N0, hN0, ?_⟩
  intro N hlarge K cuts hN rho chi xi P W G hG
  rcases hG with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hM, _, hd, _⟩
  have ht := htest N hlarge k K cuts (coldRelativeSet cuts hN P W G) hM hd
  have hp := Ascent.probability_mono (fixedCountPMF cuts)
    (fun ω h => localized_edge_event_implies_scan cuts
      (coldRelativeSet cuts hN P W G) (prefixAt W.ms G.ambient) (kappa eta/5) ω h)
  exact (sub_le_sub_right hp ε).trans ht

end RiffleLowerV2.EmpiricalLower
