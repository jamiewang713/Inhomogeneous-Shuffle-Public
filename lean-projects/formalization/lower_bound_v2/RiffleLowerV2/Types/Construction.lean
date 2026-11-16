import RiffleLowerV2.Types.Counting
import RiffleLowerV2.Types.Truncation
import RiffleLowerV2.Types.MassBins

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Types
open TimeProfile

/-- The fixed digit-order cumulative rounding, before selection of a mass bin. -/
def initialTypeData {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (xi alpha : ℝ) : RoundedTypeData P :=
  { count := fun i => roundedCount (cellPositionCount cuts hN P I i)
      (retainedTilt P xi alpha i)
    binIndex := 0 }

theorem initialTypeData_total {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hk : 2 ≤ k) (P : BorelPartition k) (I : Finset (Fin K))
    {xi alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (i : Fin P.cellCount) :
    ∑ l, (initialTypeData cuts hN P I xi alpha).count i l =
      cellPositionCount cuts hN P I i :=
  roundedCount_sum _ _ (retainedTilt_nonneg P xi alpha i)
    (retainedTilt_sum hk P hxi hxiK i)

theorem initialTypeData_support {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (xi alpha : ℝ)
    (i : Fin P.cellCount) (l : Fin k) (hl : prob (P.rep i) l ≤ 2*xi) :
    (initialTypeData cuts hN P I xi alpha).count i l = 0 :=
  roundedCount_zero _ _ l (retainedTilt_eq_zero_of_omitted P xi alpha i l hl)

theorem initialTypeData_error {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (xi alpha : ℝ)
    (i : Fin P.cellCount) (l : Fin k) :
    |((initialTypeData cuts hN P I xi alpha).count i l : ℝ) -
      (cellPositionCount cuts hN P I i : ℝ) * retainedTilt P xi alpha i l| ≤ 1 :=
  roundedCount_error _ _ (retainedTilt_nonneg P xi alpha i) l

theorem initialTypeData_nonempty {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hk : 2 ≤ k) (P : BorelPartition k) (I : Finset (Fin K))
    {xi alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ))) :
    (roundedClass cuts hN P I (initialTypeData cuts hN P I xi alpha)).Nonempty :=
  roundedClass_nonempty cuts hN P I _ (initialTypeData_total cuts hN hk P I hxi hxiK)

/-- Deterministically rounded counts and the least maximal integer mass bin. -/
def constructedTypeData {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hk : 2 ≤ k) (P : BorelPartition k) (I : Finset (Fin K))
    {xi : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ))) (alpha : ℝ) :
    RoundedTypeData P :=
  selectBinData cuts hN P I (initialTypeData cuts hN P I xi alpha)
    (initialTypeData_nonempty cuts hN hk P I hxi hxiK)

@[simp] theorem constructedTypeData_count {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (hk : 2 ≤ k) (P : BorelPartition k) (I : Finset (Fin K))
    {xi : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ))) (alpha : ℝ)
    (i : Fin P.cellCount) (l : Fin k) :
    (constructedTypeData cuts hN hk P I hxi hxiK alpha).count i l =
      roundedCount (cellPositionCount cuts hN P I i) (retainedTilt P xi alpha i) l := rfl

@[simp] theorem roundedClass_constructedTypeData {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (hk : 2 ≤ k) (P : BorelPartition k) (I : Finset (Fin K))
    {xi : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ))) (alpha : ℝ) :
    roundedClass cuts hN P I (constructedTypeData cuts hN hk P I hxi hxiK alpha) =
      roundedClass cuts hN P I (initialTypeData cuts hN P I xi alpha) := rfl

/-- All exact finite type and mass-bin specifications, uniformly in every real tilt. -/
theorem constructedTypeData_spec {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hN2 : 2 ≤ N) (hk : 2 ≤ k) (P : BorelPartition k) (I : Finset (Fin K))
    {xi C : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hreg : P.IsRegular xi C) (alpha : ℝ) :
    TypeDataSpec cuts hN P I xi alpha
      (constructedTypeData cuts hN hk P I hxi hxiK alpha) := by
  have hxi1 : xi ≤ 1 := by
    have := (cutoff_small hk hxi hxiK).1
    linarith
  exact typeDataSpec_of_counts cuts hN hN2 P I _ hxi hxi1 hreg
    (initialTypeData_total cuts hN hk P I hxi hxiK)
    (initialTypeData_support cuts hN P I xi alpha)
    (initialTypeData_error cuts hN P I xi alpha)
    (retainedTilt_denominator_pos hk P hxi hxiK)
    (initialTypeData_nonempty cuts hN hk P I hxi hxiK)
    (roundedClass_card cuts hN P I _ (initialTypeData_total cuts hN hk P I hxi hxiK))

theorem exists_typeDataSpec {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hN2 : 2 ≤ N) (hk : 2 ≤ k) (P : BorelPartition k) (I : Finset (Fin K))
    {xi C : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hreg : P.IsRegular xi C) (alpha : ℝ) :
    ∃ D : RoundedTypeData P, TypeDataSpec cuts hN P I xi alpha D :=
  ⟨constructedTypeData cuts hN hk P I hxi hxiK alpha,
    constructedTypeData_spec cuts hN hN2 hk P I hxi hxiK hreg alpha⟩

end RiffleLowerV2.Types
