import RiffleUpperV2.Contracts.V1.Main

namespace RiffleUpperV2.Audit
open RiffleUpperV2.Exploration

example {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (ω ω' : Sample cuts) : naturalHistory cuts p d 0 ω = naturalHistory cuts p d 0 ω' := by
  funext r
  simp only [Exploration.naturalHistory, Nat.not_lt_zero, ↓reduceIte]

example {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g ξ : ℝ)
    (p : Fin k) (d : Direction) (ω ω' : Sample cuts) :
    remainingDirectionalCount cuts D g ξ p d (pileSize cuts p) ω ω' = 0 := by
  simp [remainingDirectionalCount]

example {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g ξ ε : ℝ)
    (p : Fin k) (d : Direction) (ω : Sample cuts × Sample cuts) :
    pairHistoryGood cuts D g ξ ε p d 0 ω := by
  simp [pairHistoryGood]

end RiffleUpperV2.Audit

set_option pp.explicit true
set_option pp.proofs false
#print RiffleUpperV2.Contracts.V1.C
#print RiffleUpperV2.Contracts.V1.REmpiricalBound
#print axioms RiffleUpperV2.independentPair_expect
#print axioms RiffleUpperV2.positive_history_has_representative
