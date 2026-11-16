import RiffleLowerV2.Model.Main

noncomputable section
namespace RiffleUpperV2

/-- The existing concrete PMF is the primary probability API. -/
abbrev Cuts := TimeProfile.Cuts
abbrev Sample {k n L : ℕ} (cuts : Cuts k n L) := RiffleLowerV2.Sample cuts
abbrev Word := RiffleLowerV2.Word
abbrev Prefix := RiffleLowerV2.Prefix
abbrev Permutation := RiffleLowerV2.Permutation
abbrev PathEdges := RiffleLowerV2.PathEdges
abbrev expect := @RiffleLowerV2.expect
abbrev probability := @RiffleLowerV2.probability
abbrev tv := @RiffleLowerV2.tv
abbrev fixedCountPMF := @TimeProfile.fixedCountPMF
abbrev physicalInverseLaw := @RiffleLowerV2.physicalInverseLaw
abbrev uniformPermutation := RiffleLowerV2.uniformPermutation
abbrev shuffleEdges := @RiffleLowerV2.shuffleEdges
abbrev sortedWord := @RiffleLowerV2.sortedWord
abbrev rowWord := @RiffleLowerV2.rowWord
abbrev prefixMass := @RiffleLowerV2.prefixMass
abbrev prefixCount := @RiffleLowerV2.prefixCount
abbrev prefixMean := @RiffleLowerV2.prefixMean
abbrev lowerRank := @RiffleLowerV2.lowerRank
abbrev upperRank := @RiffleLowerV2.upperRank

/-- `r : Fin L` denotes absolute manuscript column `a+r+1`. -/
def absoluteColumn {L : ℕ} (a : ℕ) (r : Fin L) : ℕ := a + r.val + 1

theorem absoluteColumn_bounds {L : ℕ} (a : ℕ) (r : Fin L) :
    a < absoluteColumn a r ∧ absoluteColumn a r ≤ a + L := by
  dsimp [absoluteColumn]; omega

/-- The physical law is reused, never replaced by the graph law by definition. -/
theorem physical_graph_representation {k n L : ℕ} (cuts : Cuts k n L) :
    physicalInverseLaw cuts = RiffleLowerV2.graphMixtureLaw cuts :=
  RiffleLowerV2.Model.physical_graph_representation cuts

/-- Two independently drawn matrices; expectation is an iterated finite sum. -/
def expectedCommonEdges {k n L : ℕ} (cuts : Cuts k n L) : ℝ :=
  expect (fixedCountPMF cuts) (fun ω =>
    expect (fixedCountPMF cuts) (fun ω' =>
      ((shuffleEdges ω ∩ shuffleEdges ω').card : ℝ)))

end RiffleUpperV2
