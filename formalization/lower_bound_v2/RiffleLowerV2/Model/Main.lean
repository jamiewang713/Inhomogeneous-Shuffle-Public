import RiffleLowerV2.Model.Sorting
import RiffleLowerV2.Model.GraphLaw
import RiffleLowerV2.Model.ComponentFibers
import RiffleLowerV2.Model.Physical

noncomputable section
namespace RiffleLowerV2.Model

/-- The physical inverse shuffle is the independently sampled graph-component mixture. -/
theorem physical_graph_representation {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) :
    physicalInverseLaw cuts = graphMixtureLaw cuts :=
  (physicalMatrixBridge cuts).trans (graphRepresentation cuts)

/-- Ready-to-use permutation test identity for the chronological physical shuffle. -/
theorem physical_graph_event {k N K : ℕ} (cuts : TimeProfile.Cuts k N K)
    (A : Permutation N → Prop) :
    probability (physicalInverseLaw cuts) A = expect (TimeProfile.fixedCountPMF cuts) (fun ω =>
      probability (uniformPermutation N) (fun π => A (componentSort (shuffleEdges ω) π))) := by
  rw [physicalMatrixBridge cuts]
  exact graphEventIdentity cuts A

end RiffleLowerV2.Model
