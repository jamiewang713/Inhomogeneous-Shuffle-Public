import RiffleUpperV2.Shared.Profile

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2

def countEncoding {k n L : ℕ} (cuts : Cuts k n L) : Fin L → Fin k → Fin (n+1) :=
  fun j d => ⟨cuts.count j d, by
    have h := Finset.single_le_sum (fun x (_ : x ∈ Finset.univ) =>
      Nat.zero_le (cuts.count j x)) (Finset.mem_univ d)
    rw [cuts.sum_count] at h
    omega⟩

theorem countEncoding_injective {k n L : ℕ} :
    Function.Injective (@countEncoding k n L) := by
  intro c d h
  have hc : c.count = d.count := by
    funext j a
    exact congrArg Fin.val (congrFun (congrFun h j) a)
  cases c; cases d; cases hc; rfl

instance cutsFintype (k n L : ℕ) : Fintype (Cuts k n L) :=
  Fintype.ofInjective countEncoding countEncoding_injective

/-- The environment is the entire count array, with an arbitrary joint law. -/
def randomInverseLaw {k n L : ℕ} (Q : PMF (Cuts k n L)) : PMF (Permutation n) :=
  Q.bind physicalInverseLaw

end RiffleUpperV2
