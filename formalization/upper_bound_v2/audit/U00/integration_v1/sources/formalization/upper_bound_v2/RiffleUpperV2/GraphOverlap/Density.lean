import RiffleUpperV2.GraphOverlap.Support

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2 RiffleLowerV2.Model
variable {N : ℕ}

def graphLaw (G : PathEdges N) : PMF (Permutation N) :=
  (RiffleLowerV2.uniformPermutation N).map (componentSort G)

def density (G : PathEdges N) (σ : Permutation N) : ℝ :=
  if BlockIncreasing G σ then componentFactorial G else 0

theorem density_nonneg (G : PathEdges N) (σ : Permutation N) : 0 ≤ density G σ := by
  unfold density
  split_ifs <;> positivity

theorem uniform_mass (σ : Permutation N) :
    ((RiffleLowerV2.uniformPermutation N) σ).toReal = 1 / (Fintype.card (Permutation N) : ℝ) := by
  simp [RiffleLowerV2.uniformPermutation, PMF.uniformOfFintype_apply]

theorem graphLaw_mass (G : PathEdges N) (σ : Permutation N) :
    (graphLaw G σ).toReal = density G σ / Fintype.card (Permutation N) := by
  rw [← expect_singleton, graphLaw, expect_map]
  change RiffleLowerV2.expect (PMF.uniformOfFintype _) _ = _
  rw [expect_uniform]
  congr 1
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (componentSort_fiber_card_eq G σ)
  simp only [ComponentSortFiber, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    density] at hc
  convert hc using 1
  · apply Finset.sum_congr rfl
    intro π _
    split_ifs <;> rfl
  · rfl

theorem graphLaw_density (G : PathEdges N) (σ : Permutation N) :
    (graphLaw G σ).toReal = ((RiffleLowerV2.uniformPermutation N) σ).toReal * density G σ := by
  rw [graphLaw_mass, uniform_mass]
  ring

theorem density_normalized (G : PathEdges N) :
    RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) (density G) = 1 := by
  calc
    _ = RiffleLowerV2.expect (graphLaw G) (fun _ => 1) := by
      unfold RiffleLowerV2.expect
      simp only [mul_one, graphLaw_density]
    _ = 1 := expect_const _ _

theorem increasing_probability (G : PathEdges N) :
    RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) (BlockIncreasing G) =
      1 / (componentFactorial G : ℝ) := by
  have hpos : (componentFactorial G : ℝ) ≠ 0 := by exact_mod_cast (componentFactorial_pos G).ne'
  apply (eq_div_iff hpos).mpr
  rw [← density_normalized G]
  unfold RiffleLowerV2.probability RiffleLowerV2.expect density
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp_all

def overlap (G H : PathEdges N) : ℝ :=
  RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) (fun σ => density G σ * density H σ)

theorem overlap_nonneg (G H : PathEdges N) : 0 ≤ overlap G H := by
  apply Finset.sum_nonneg
  intro σ _
  exact mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (density_nonneg G σ) (density_nonneg H σ))

/-- Exact overlap for arbitrary path graphs, including their arbitrary union. -/
theorem overlapIdentity (G H : PathEdges N) :
    overlap G H = (componentFactorial G : ℝ) * componentFactorial H /
      componentFactorial (G ∪ H) := by
  have hp (σ : Permutation N) : density G σ * density H σ =
      (if BlockIncreasing (G ∪ H) σ then (1 : ℝ) else 0) *
        ((componentFactorial G : ℝ) * componentFactorial H) := by
    simp only [blockIncreasing_union, density]
    split_ifs <;> simp_all
  calc
    overlap G H = RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) (BlockIncreasing (G ∪ H)) *
        ((componentFactorial G : ℝ) * componentFactorial H) := by
      unfold overlap RiffleLowerV2.probability RiffleLowerV2.expect
      simp only [hp, Finset.sum_mul, mul_assoc]
    _ = _ := by rw [increasing_probability]; ring

end RiffleUpperV2.GraphOverlap
