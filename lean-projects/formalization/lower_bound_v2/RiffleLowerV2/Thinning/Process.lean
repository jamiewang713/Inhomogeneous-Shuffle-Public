import RiffleLowerV2.Thinning.Sampling
import RiffleLowerV2.Thinning.Recursion
import RiffleLowerV2.Thinning.Tails

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Thinning

private theorem ratio_bounds {M m : ℕ} (hM : 0 < M) (hm : m ≤ M) :
    0 ≤ (m : ℝ)/M ∧ (m : ℝ)/M ≤ 1 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  exact ⟨by positivity, (div_le_one hMr).2 (by exact_mod_cast hm)⟩

theorem thinningQ_bounds {M d : ℕ} (hM : 0 < M) (m : Fin d → ℕ)
    (hm : ∀ j, m j ≤ M) : 0 ≤ Targets.thinningQ M m ∧ Targets.thinningQ M m ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun j _ => (ratio_bounds hM (hm j)).1),
    Finset.prod_le_one (fun j _ => (ratio_bounds hM (hm j)).1)
      (fun j _ => (ratio_bounds hM (hm j)).2)⟩

/-- Successive uniform subsets are handled by exact finite column integration. -/
theorem successiveThinning : Targets.SuccessiveThinning := by
  intro M d hM m hm s hs
  let S : Fin d → Permutation M → Finset (Fin M) :=
    fun j σ => Finset.univ.filter fun i => (σ.symm i).val < m j
  let q : Fin d → ℝ := fun j => (m j : ℝ)/M
  have hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1 := fun j => ratio_bounds hM (hm j)
  have hstep : ∀ j (A : Finset (Fin M)) (z : ℝ), 0 < z →
      expect (PMF.uniformOfFintype (Permutation M)) (fun σ => z^(A ∩ S j σ).card) ≤
        (1-q j+q j*z)^A.card := by
    intro j A z hz
    have hb : (Finset.univ.filter (fun i : Fin M => i.val < m j)).card = m j := by
      simpa [min_eq_right (hm j)] using (Fin.card_filter_val_lt (n := M) (m := m j))
    have h := permutation_intersection_transform A
      (Finset.univ.filter fun i : Fin M => i.val < m j) hz
    simpa only [map_initial_eq, hb, S, q, uniformPermutation] using h
  have h := independent_intersection_transform M d (fun _ => Permutation M) S q hq hstep
    Finset.univ s hs
  have hc (ω : Fin d → Permutation M) :
      (intersectionWithin Finset.univ S ω).card = Targets.thinningCount m ω := by
    simp [intersectionWithin, Targets.thinningCount, S]
  refine ⟨?_, ?_⟩
  · simpa only [hc, Finset.card_univ, Fintype.card_fin, q, Targets.thinningQ] using h
  · exact binomial_le_exp (thinningQ_bounds hM m hm).1 (thinningQ_bounds hM m hm).2 hs

/-- All three tails for the abstract subset process, including zero means and
empty column sequences on the explicit positive-population domain. -/
theorem thinningTails (M d : ℕ) (hM : 0 < M) (m : Fin d → ℕ) (hm : ∀ j, m j ≤ M) :
    (∀ t : ℝ, 0 < t →
      probability (PMF.uniformOfFintype (Fin d → Permutation M))
        (fun ω => t ≤ |(Targets.thinningCount m ω : ℝ) - M*Targets.thinningQ M m|) ≤
        2*Real.exp (-t^2/(4*(M*Targets.thinningQ M m+t)))) ∧
    probability (PMF.uniformOfFintype (Fin d → Permutation M))
      (fun ω => (Targets.thinningCount m ω : ℝ) ≤ M*Targets.thinningQ M m/2) ≤
      Real.exp (-chernoffConstant*(M*Targets.thinningQ M m)) ∧
    probability (PMF.uniformOfFintype (Fin d → Permutation M))
      (fun ω => Targets.thinningCount m ω < 2) ≤ 2*Real.exp (-(M*Targets.thinningQ M m)/2) := by
  let P := PMF.uniformOfFintype (Fin d → Permutation M)
  let μ : ℝ := M*Targets.thinningQ M m
  have hμ : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg M) (thinningQ_bounds hM m hm).1
  have ht : ∀ s : ℝ, 0 < s → expect P (fun ω => s^Targets.thinningCount m ω) ≤ Real.exp (μ*(s-1)) := by
    intro s hs
    exact le_trans (successiveThinning M d hM m hm s hs).1 (successiveThinning M d hM m hm s hs).2
  exact ⟨fun _ h => bernstein_of_transform P _ μ hμ ht h,
    half_mean_of_transform P _ μ ht, less_two_of_transform P _ μ ht⟩

end RiffleLowerV2.Thinning
