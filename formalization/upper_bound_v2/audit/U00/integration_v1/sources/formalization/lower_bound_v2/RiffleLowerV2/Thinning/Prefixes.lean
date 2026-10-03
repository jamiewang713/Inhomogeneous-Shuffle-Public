import RiffleLowerV2.Thinning.ColumnSampling
import RiffleLowerV2.Thinning.PrefixCoordinates
import RiffleLowerV2.Thinning.Recursion
import RiffleLowerV2.Thinning.Tails
import RiffleLowerV2.Thinning.AllPrefixes
import RiffleLowerV2.Thinning.MaximalWord

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Thinning
open TimeProfile

theorem prefixCount_intersectionWithin {k N K : ℕ} {cuts : Cuts k N K}
    (w : Prefix k K) (ω : Sample cuts) :
    prefixCount w ω = (intersectionWithin Finset.univ (prefixColumnSet cuts w) ω).card := by
  unfold prefixCount
  congr 1
  ext i
  simp only [intersectionWithin, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [prefix_coordinates_iff]
  constructor
  · intro h j
    by_cases hj : j.val < w.1.val
    · have he := h ⟨j.val,hj⟩
      simpa [prefixColumnSet, hj, sampleEntry] using he
    · simp [prefixColumnSet, hj]
  · intro h j
    have he := h (Fin.castLE (Nat.le_of_lt_succ w.1.isLt) j)
    simpa [prefixColumnSet, j.isLt, sampleEntry] using he

/-- Concrete fixed-column prefix transform for all lengths and positive s. -/
theorem prefixTransform {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (w : Prefix k K) (s : ℝ) (hs : 0 < s) :
    expect (fixedCountPMF cuts) (fun ω => s^prefixCount w ω) ≤
      (1-prefixMass cuts w+prefixMass cuts w*s)^N ∧
    (1-prefixMass cuts w+prefixMass cuts w*s)^N ≤ Real.exp (prefixMean cuts w*(s-1)) := by
  have hq := prefixColumnFraction_bounds cuts hN w
  have hstep : ∀ j (A : Finset (Fin N)) (z : ℝ), 0 < z →
      expect (PMF.uniformOfFintype (ColumnAssignments cuts j))
        (fun c => z^(A ∩ prefixColumnSet cuts w j c).card) ≤
        (1-prefixColumnFraction cuts w j+prefixColumnFraction cuts w j*z)^A.card := by
    intro j A z hz
    by_cases hj : j.val < w.1.val
    · simpa only [prefixColumnSet, prefixColumnFraction, dif_pos hj, columnPMF] using
        column_intersection_transform cuts j (w.2.get ⟨j.val,hj⟩) A hz
    · simp [prefixColumnSet, prefixColumnFraction, hj, uniform_expect_const]
  have h := independent_intersection_transform N K (ColumnAssignments cuts)
    (prefixColumnSet cuts w) (prefixColumnFraction cuts w) hq hstep Finset.univ s hs
  have hQ0 : 0 ≤ prefixMass cuts w := by
    rw [← prefixColumnFraction_product cuts w]
    exact Finset.prod_nonneg fun j _ => (hq j).1
  have hQ1 : prefixMass cuts w ≤ 1 := by
    rw [← prefixColumnFraction_product cuts w]
    exact Finset.prod_le_one (fun j _ => (hq j).1) (fun j _ => (hq j).2)
  refine ⟨?_, binomial_le_exp hQ0 hQ1 hs⟩
  simp only [Finset.card_univ, Fintype.card_fin, prefixColumnFraction_product] at h
  change expect (fixedCountPMF cuts)
    (fun ω : Sample cuts => s^(intersectionWithin Finset.univ (prefixColumnSet cuts w) ω).card) ≤ _ at h
  simpa only [← prefixCount_intersectionWithin] using h

theorem prefixTails : Targets.PrefixTails := by
  intro k N K cuts hN w
  have htr : ∀ s : ℝ, 0 < s →
      expect (fixedCountPMF cuts) (fun ω => s^prefixCount w ω) ≤ Real.exp (prefixMean cuts w*(s-1)) := by
    intro s hs
    exact le_trans (prefixTransform cuts hN w s hs).1 (prefixTransform cuts hN w s hs).2
  exact ⟨fun _ ht => bernstein_of_transform _ _ _ (prefixMean_nonneg cuts w) htr ht,
    half_mean_of_transform _ _ _ htr, less_two_of_transform _ _ _ htr⟩

theorem allPrefixConcentration : Targets.AllPrefixConcentration :=
  allPrefixConcentration_of_prefixTails prefixTails

/-- The maximizing word is chosen from the cuts before sampling. The subsequent
permutation-run and TV conclusions are separate downstream obligations. -/
theorem maximalWordTail {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) :
    ∃ w : Word k K, IsCanonicalMaxWord cuts w ∧
      wordMass cuts w*N = maximalMean cuts hN ∧
      ∀ m : ℕ, (m : ℝ) ≤ maximalMean cuts hN/2 →
        probability (fixedCountPMF cuts) (fun ω => wordCount w ω < m) ≤
          Real.exp (-chernoffConstant*maximalMean cuts hN) := by
  obtain ⟨w, hw⟩ := exists_canonicalMaxWord cuts hN
  have hmean := canonicalMaxWord_mean cuts hN w hw
  refine ⟨w, hw, by simpa [mul_comm] using hmean, ?_⟩
  intro m hm
  have h := (prefixTails cuts hN (fullPrefix w)).2.1
  have he : prefixMean cuts (fullPrefix w) = maximalMean cuts hN := hmean
  rw [he] at h
  apply le_trans _ h
  apply probability_mono
  intro ω hω
  have hc : (wordCount w ω : ℝ) < m := by exact_mod_cast hω
  change (wordCount w ω : ℝ) ≤ maximalMean cuts hN/2
  linarith

end RiffleLowerV2.Thinning
