import RiffleUpperV2.Anchor.Definitions

noncomputable section
namespace RiffleUpperV2

abbrev edgeLeft := @RiffleLowerV2.edgeLeft
abbrev edgeRight := @RiffleLowerV2.edgeRight
abbrev manuscriptRank := @RiffleLowerV2.manuscriptRank
abbrev componentIndex := @RiffleLowerV2.componentIndex
abbrev componentSort := @RiffleLowerV2.componentSort

/-- The first retained column is a+1; future prefix length excludes this anchor. -/
def anchoredAbsoluteEnd {k d : ℕ} (a : ℕ) (x : Prefix k d) : ℕ := a+1+x.1.val

theorem anchoredAbsoluteEnd_bounds {k d : ℕ} (a : ℕ) (x : Prefix k d) :
    a+1 ≤ anchoredAbsoluteEnd a x ∧ anchoredAbsoluteEnd a x ≤ a+1+d := by
  have := x.1.isLt
  dsimp [anchoredAbsoluteEnd]
  omega

/-- Integer half-open rank interval, with an explicit arbitrary absolute offset. -/
def anchoredInterval {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) : Finset ℤ :=
  Finset.Ico (Anchor.lowerEndpoint c₀ R x ω) (Anchor.upperEndpoint c₀ R x ω)

theorem anchoredInterval_card {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    (anchoredInterval c₀ R x ω).card = (Anchor.prefixRows R x ω).card := by
  simp [anchoredInterval, Anchor.upperEndpoint]

end RiffleUpperV2
