import RiffleUpperV2.Shared.Infimum
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section
open Set Filter
open scoped ENNReal BigOperators
namespace RiffleUpperV2
open TimeProfile

abbrev ScalarIntegrable := @RiffleLowerV2.ScalarIntegrable
abbrev macroBeta := @RiffleLowerV2.macroBeta
abbrev macroLambda1 := @RiffleLowerV2.macroLambda1

/-- A legitimate fixed common source constant, certified by partition existence. -/
def regularityConstant (_k : ℕ) : ℝ := 1

theorem regularPartitions_exist {k : ℕ} (hk : 2 ≤ k) {χ : ℝ}
    (hχ : 0 < χ) (hχk : χ < 1 / (k : ℝ)) :
    ∃ P : BorelPartition k, P.IsRegular χ (regularityConstant k) :=
  exists_regular_partition hk hχ hχk

def reducedMargin {k : ℕ} (μ : TimeLaw k) (T : ℝ) : ℝ :=
  max (macroBeta μ T) (macroLambda1 μ T)

/-- Empty negativity sets have infimum infinity in this complete lattice. -/
def criticalTime {k : ℕ} (μ : TimeLaw k) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {T : ℝ | 0 < T ∧ reducedMargin μ T < 0})

theorem criticalTime_empty {k : ℕ} (μ : TimeLaw k)
    (h : ¬ ∃ T : ℝ, 0 < T ∧ reducedMargin μ T < 0) : criticalTime μ = ⊤ := by
  have he : {T : ℝ | 0 < T ∧ reducedMargin μ T < 0} = ∅ := by
    ext T
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro hT
    exact h ⟨T, hT⟩
  simp [criticalTime, he]

/-- One sequence per N, with all finite horizons defined by restriction. -/
structure InfiniteCuts (k n : ℕ) where
  count : ℕ → Fin k → ℕ
  sum_count : ∀ j, ∑ d, count j d = n

def InfiniteCuts.take {k n : ℕ} (cuts : InfiniteCuts k n) (K : ℕ) : Cuts k n K :=
  ⟨fun j => cuts.count j.val, fun j => cuts.sum_count j.val⟩

def ArbitrarilyFineApproximation {k : ℕ} (μ : TimeLaw k)
    (cuts : ∀ N : ℕ, InfiniteCuts k N) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ χstar : ℝ, 0 < χstar →
  ∃ χ : ℝ, 0 < χ ∧ χ ≤ χstar ∧
  ∃ P : BorelPartition k, P.IsRegular χ (regularityConstant k) ∧
    ScalarIntegrable μ P T ∧
  ∃ g γ ρbar : ℝ, 0 < g ∧ g < 1/(k : ℝ) ∧ 0 < γ ∧ 0 < ρbar ∧
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρbar → ∀ φ : ℝ, 0 < φ →
  ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
  ∀ (N : ℕ) (hN : N0 ≤ N),
    AlmostLike ((cuts N).take (horizonDepth N T)) (by omega) μ P T ρ φ ∧
    LocalGood ((cuts N).take (horizonDepth N T)) (by omega) g γ ρ 0 T

def mixingTime {k N : ℕ} (cuts : InfiniteCuts k N) (ε : ℝ) : ℝ≥0∞ :=
  sInf ((fun m : ℕ => (m : ℝ≥0∞)) ''
    {m : ℕ | tv (physicalInverseLaw (cuts.take m)) (uniformPermutation N) ≤ ε})

theorem mixingTime_empty {k N : ℕ} (cuts : InfiniteCuts k N) (ε : ℝ)
    (h : ∀ m, ε < tv (physicalInverseLaw (cuts.take m)) (uniformPermutation N)) :
    mixingTime cuts ε = ⊤ := by
  have he : {m : ℕ | tv (physicalInverseLaw (cuts.take m)) (uniformPermutation N) ≤ ε} = ∅ := by
    ext m
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_le.mpr (h m)
  simp [mixingTime, he]

end RiffleUpperV2
