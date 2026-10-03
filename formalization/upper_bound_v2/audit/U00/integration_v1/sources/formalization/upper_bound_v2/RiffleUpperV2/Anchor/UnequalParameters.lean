import RiffleUpperV2.Anchor.UnequalGood
import RiffleUpperV2.Shared.UnequalVariance

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric

theorem residualAllowed_eq_filter {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c : ColumnAssignments cuts j) :
    residualAllowed A D c = (Finset.univ \ A).filter (fun r => c.val r ∈ D) := by
  apply Finset.ext
  intro r
  simp only [residualAllowed, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

theorem residualAllowed_partition_card {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c : ColumnAssignments cuts j) :
    (residualAllowed A D c).card + (residualAllowed A (Finset.univ \ D) c).card = n-A.card := by
  rw [residualAllowed_eq_filter, residualAllowed_eq_filter]
  have he : (Finset.univ \ A).filter (fun r => c.val r ∈ Finset.univ \ D) =
      (Finset.univ \ A).filter (fun r => c.val r ∉ D) := by
    apply Finset.filter_congr
    intro r _
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [he, Finset.card_filter_add_card_filter_not,
    Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]

theorem unequalEndpointParams_counts {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    let P := unequalEndpointParams s R x j ω
    let A := unequalExposedRows s R x j ω
    let D := s.allowed (x.2.get j)
    P.population = n-A.card ∧
    P.marked = (residualAllowed A D (ω (prefixColumn x j))).card ∧
    P.draws = (unequalSampleRows s R x j ω).card ∧
    P.population-P.marked = (residualAllowed A (Finset.univ \ D) (ω (prefixColumn x j))).card := by
  dsimp only
  have hpop : (unequalEndpointParams s R x j ω).population = n-(unequalExposedRows s R x j ω).card :=
    sourceSamplingParams_population _ _ _ _ _
  have hmark : (unequalEndpointParams s R x j ω).marked =
      (residualAllowed (unequalExposedRows s R x j ω) (s.allowed (x.2.get j)) (ω (prefixColumn x j))).card :=
    (residualAllowed_card _ _ _ _ (fun _ _ => rfl)).symm
  refine ⟨hpop,hmark,rfl,?_⟩
  have hpart := residualAllowed_partition_card (unequalExposedRows s R x j ω)
    (s.allowed (x.2.get j)) (ω (prefixColumn x j))
  rw [hpop,hmark]
  omega

/-- The actual unequal good event supplies all raw count inputs for the
finite-population variance bound, including the sample complement reserve. -/
theorem unequalVariance_good_counts {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    (hji : j.val < i.val) {g : ℝ} (hg : Reserve R g)
    (hw : 0 < witnessMean cuts s R x i j) (ω : Sample cuts) (hgood : unequalGood cuts s R x i j ω) :
    g * witnessMean cuts s R x i j * ((allowedCount cuts (prefixColumn x j) (s.allowed (x.2.get j)) : ℝ)/n) *
      ((allowedCount cuts (prefixColumn x j) (Finset.univ \ s.allowed (x.2.get j)) : ℝ)/n) / 8 ≤
      (unequalEndpointParams s R x j ω).varianceFormula := by
  let P := unequalEndpointParams s R x j ω
  let A := unequalExposedRows s R x j ω
  let D := s.allowed (x.2.get j)
  have hc := unequalEndpointParams_counts s R x j ω
  change P.population = n-A.card ∧ P.marked = _ ∧ P.draws = _ ∧ P.population-P.marked = _ at hc
  have hpop : (P.population : ℝ) = (n : ℝ)-A.card := by
    rw [hc.1, Nat.cast_sub (by simpa using Finset.card_le_univ A : A.card ≤ n)]
  have hdraw : witnessMean cuts s R x i j/2 ≤ (P.draws : ℝ) := by
    rw [hc.2.2.1]
    exact hgood.1.trans (by exact_mod_cast (Finset.card_le_card
      (witnessRows_subset_unequalSample cuts s R x i j hji ω)))
  have hdpos : (0 : ℝ) < P.draws := lt_of_lt_of_le (by positivity) hdraw
  have hNpos : (0 : ℝ) < P.population := hdpos.trans_le (by exact_mod_cast P.draws_le)
  apply unequalVarianceFromCounts P (by exact_mod_cast hn) (Nat.cast_nonneg A.card)
    hw (by positivity) (by positivity) hg.1 hg.2.2 hpop ?_ hdraw ?_ ?_
  · rw [hc.2.2.1]
    exact_mod_cast unequalTotal_card_le s R x j ω
  · apply (le_div_iff₀ hNpos).mpr
    rw [hc.2.1, hpop]
    have hh := hgood.2.1
    change ((n : ℝ)-A.card)*((allowedCount cuts (prefixColumn x j) D : ℝ)/n)/2 ≤ _ at hh
    nlinarith
  · apply (le_div_iff₀ hNpos).mpr
    have he : (P.population : ℝ)-P.marked =
        (residualAllowed A (Finset.univ \ D) (ω (prefixColumn x j))).card := by
      rw [← Nat.cast_sub P.marked_le, hc.2.2.2]
    rw [he,hpop]
    have hh := hgood.2.2
    change ((n : ℝ)-A.card)*((allowedCount cuts (prefixColumn x j) (Finset.univ \ D) : ℝ)/n)/2 ≤ _ at hh
    nlinarith

end RiffleUpperV2.Anchor
