import RiffleLowerV2.Localization.Endpoints.Error

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization
open TimeProfile

theorem relativeLowerMean_eq_side_sum {k N K l m : ℕ} (cuts : Cuts k N K)
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K) (x : WordOn k (columnSet K l m)) :
    prefixMean cuts (prefixAt l a)*relativeMassBefore cuts x =
      ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => d < x j),
        prefixMean cuts (sidePrefix a l m x j d) := by
  by_cases hN : 0 < N
  · rw [relativeMassBefore_eq_sideWeight cuts hN]
    simp_rw [prefixMean_sidePrefix cuts a hlm hm x, Finset.mul_sum]
  · have hzero : N = 0 := by omega
    subst N
    simp [prefixMean]

theorem relativeUpperMean_eq_side_sum {k N K l m : ℕ} (cuts : Cuts k N K)
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K) (x : WordOn k (columnSet K l m)) :
    prefixMean cuts (prefixAt l a)*(relativeMassBefore cuts x+massOn cuts x) =
      prefixMean cuts (prefixAt l a) -
      ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => x j < d),
        prefixMean cuts (sidePrefix a l m x j d) := by
  by_cases hN : 0 < N
  · have ht := relativeMass_total cuts hN x
    have hrel : relativeMassBefore cuts x+massOn cuts x = 1-relativeMassAfter cuts x := by linarith
    rw [hrel, relativeMassAfter_eq_sideWeight cuts hN]
    simp only [prefixMean_sidePrefix cuts a hlm hm x, mul_sub, mul_one, Finset.mul_sum]
  · have hzero : N = 0 := by omega
    subst N
    simp [prefixMean]

theorem relativeEndpoint_identities {k N K l m : ℕ} (cuts : Cuts k N K)
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K)
    (x : WordOn k (columnSet K l m)) (omega : Sample cuts) :
    ((relativeLowerCount a l m x omega : ℝ)-prefixMean cuts (prefixAt l a)*relativeMassBefore cuts x =
      ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => d < x j),
        ((prefixCount (sidePrefix a l m x j d) omega : ℝ)-prefixMean cuts (sidePrefix a l m x j d))) ∧
    ((relativeUpperCount a l m x omega : ℝ)-prefixMean cuts (prefixAt l a)*(relativeMassBefore cuts x+massOn cuts x) =
      ((prefixCount (prefixAt l a) omega : ℝ)-prefixMean cuts (prefixAt l a)) -
      ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => x j < d),
        ((prefixCount (sidePrefix a l m x j d) omega : ℝ)-prefixMean cuts (sidePrefix a l m x j d))) := by
  constructor
  · rw [relativeLowerCount_eq_side_sum a hlm hm x omega, relativeLowerMean_eq_side_sum cuts a hlm hm x]
    simp [Finset.sum_sub_distrib]
  · have hc := relativeUpper_add_greater a hlm hm x omega
    rw [relativeGreaterCount_eq_side_sum a hlm hm x omega] at hc
    rw [relativeUpperMean_eq_side_sum cuts a hlm hm x]
    simp only [Finset.sum_sub_distrib]
    linarith

/-- The exact finite endpoint theorem, including empty suffixes and zero populations. -/
theorem relativeEndpoint : Targets.RelativeEndpointTarget := by
  intro k N K cuts a l m hlm hm x omega
  have hid := relativeEndpoint_identities cuts a hlm hm x omega
  refine ⟨hid.1, hid.2, ?_⟩
  intro A hA hconc
  by_cases hN : 0 < N
  · have hleft := side_error_bound cuts hN a hlm hm x omega A hA hconc
      (fun d e : Fin k => d < e) (fun _ _ h => ne_of_lt h)
    have hright := side_error_bound cuts hN a hlm hm x omega A hA hconc
      (fun d e : Fin k => e < d) (fun _ _ h => ne_of_gt h)
    have hleft' : |∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => d < x j),
        ((prefixCount (sidePrefix a l m x j d) omega : ℝ)-prefixMean cuts (sidePrefix a l m x j d))| ≤
        A*(Real.sqrt ((k : ℝ)*K)*Real.sqrt (prefixMean cuts (prefixAt l a))+(k : ℝ)*K) := by
      convert hleft using 1
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr
      · ext d
        simp
      · intros
        rfl
    have hright' : |∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => x j < d),
        ((prefixCount (sidePrefix a l m x j d) omega : ℝ)-prefixMean cuts (sidePrefix a l m x j d))| ≤
        A*(Real.sqrt ((k : ℝ)*K)*Real.sqrt (prefixMean cuts (prefixAt l a))+(k : ℝ)*K) := by
      convert hright using 1
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr
      · ext d
        simp
      · intros
        rfl
    have hamb := hconc (prefixAt l a)
    rw [hid.1, hid.2]
    have htri := abs_sub
      ((prefixCount (prefixAt l a) omega : ℝ)-prefixMean cuts (prefixAt l a))
      (∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => x j < d),
        ((prefixCount (sidePrefix a l m x j d) omega : ℝ)-prefixMean cuts (sidePrefix a l m x j d)))
    calc
      _ ≤ A*(Real.sqrt ((k : ℝ)*K)*Real.sqrt (prefixMean cuts (prefixAt l a))+(k : ℝ)*K) +
        (A*(Real.sqrt (prefixMean cuts (prefixAt l a))+1) +
          A*(Real.sqrt ((k : ℝ)*K)*Real.sqrt (prefixMean cuts (prefixAt l a))+(k : ℝ)*K)) :=
        add_le_add hleft' (htri.trans (add_le_add hamb hright'))
      _ = _ := by ring
  · have hzero : N = 0 := by omega
    subst N
    simp only [relativeLowerCount, relativeUpperCount, prefixMean, Nat.cast_zero, zero_mul,
      sub_zero, Real.sqrt_zero, mul_zero, zero_add]
    simp
    positivity

end RiffleLowerV2.Localization
