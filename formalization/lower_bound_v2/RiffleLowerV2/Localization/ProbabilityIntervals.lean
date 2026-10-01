import RiffleLowerV2.Localization.Intervals
import RiffleLowerV2.Localization.WordOrder

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Localization
open TimeProfile
attribute [local instance] Classical.propDecidable

theorem massOn_nonnegative {k N K : ℕ} (cuts : Cuts k N K)
    {I : Finset (Fin K)} (x : WordOn k I) : 0 ≤ massOn cuts x := by
  unfold massOn
  positivity

theorem sum_massOn_eq_one {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (I : Finset (Fin K)) : (∑ x : WordOn k I, massOn cuts x) = 1 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold massOn
  rw [← Fintype.prod_sum (fun (j : I) (a : Fin k) => (cuts.count j.val a : ℝ)/N)]
  have hs (j : I) : (∑ a : Fin k, (cuts.count j.val a : ℝ)/N) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, cuts.sum_count]
    exact div_self hNr
  simp_rw [hs]
  simp

theorem massOn_le_one_of_positive_population {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) {I : Finset (Fin K)} (x : WordOn k I) : massOn cuts x ≤ 1 := by
  rw [← sum_massOn_eq_one cuts hN I]
  exact Finset.single_le_sum (fun y _ => massOn_nonnegative cuts y) (Finset.mem_univ x)

theorem prefixMean_le_population {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (v : Prefix k K) : prefixMean cuts v ≤ N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : prefixMass cuts v ≤ 1 := by
    unfold prefixMass
    apply Finset.prod_le_one
    · intro j _
      positivity
    · intro j _
      apply (div_le_one hNr).mpr
      exact_mod_cast (Finset.single_le_sum (fun a _ => Nat.zero_le _)
        (Finset.mem_univ (v.2.get j))).trans_eq
          (cuts.sum_count ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ v.1.isLt)⟩)
  exact (mul_le_mul_of_nonneg_left hp hNr.le).trans_eq (mul_one _)

theorem relativeMassBefore_nonnegative {k N K : ℕ} (cuts : Cuts k N K)
    {I : Finset (Fin K)} (x : WordOn k I) : 0 ≤ relativeMassBefore cuts x := by
  exact Finset.sum_nonneg fun y _ => massOn_nonnegative cuts y

theorem relativeMassBefore_add_mass_le_one {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) {I : Finset (Fin K)} (x : WordOn k I) :
    relativeMassBefore cuts x + massOn cuts x ≤ 1 := by
  let S := Finset.univ.filter fun v : WordOn k I => wordOnList v < wordOnList x
  have hx : x ∉ S := by simp [S]
  calc
    _ = ∑ y ∈ insert x S, massOn cuts y := by
      rw [Finset.sum_insert hx]
      exact add_comm _ _
    _ ≤ ∑ y : WordOn k I, massOn cuts y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => massOn_nonnegative cuts y)
    _ = 1 := sum_massOn_eq_one cuts hN I

theorem relativeMassBefore_add_mass_le_of_lt {k N K : ℕ} (cuts : Cuts k N K)
    {I : Finset (Fin K)} {x y : WordOn k I} (hxy : wordOnList x < wordOnList y) :
    relativeMassBefore cuts x + massOn cuts x ≤ relativeMassBefore cuts y := by
  let S := Finset.univ.filter fun v : WordOn k I => wordOnList v < wordOnList x
  let T := Finset.univ.filter fun v : WordOn k I => wordOnList v < wordOnList y
  have hx : x ∉ S := by simp [S]
  have hsub : insert x S ⊆ T := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hxy
    · exact (Finset.mem_filter.mp hz).2.trans hxy
  calc
    _ = ∑ z ∈ insert x S, massOn cuts z := by
      rw [Finset.sum_insert hx]
      exact add_comm _ _
    _ ≤ ∑ z ∈ T, massOn cuts z := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun z _ _ => massOn_nonnegative cuts z)
    _ = _ := rfl

theorem probabilityIntervals_pairwiseDisjoint {k N K : ℕ} (cuts : Cuts k N K)
    {I : Finset (Fin K)} (S : Finset (WordOn k I)) {mu : ℝ} (hmu : 0 ≤ mu) :
    (S : Set (WordOn k I)).PairwiseDisjoint (fun x =>
      integerHalfOpen (mu*relativeMassBefore cuts x)
        (mu*(relativeMassBefore cuts x+massOn cuts x))) := by
  intro x _ y _ hxy
  have hne : wordOnList x ≠ wordOnList y := fun he => hxy (wordOnList_injective he)
  rcases lt_or_gt_of_ne hne with h | h
  · exact integerHalfOpen_disjoint (mul_le_mul_of_nonneg_left
      (relativeMassBefore_add_mass_le_of_lt cuts h) hmu)
  · exact (integerHalfOpen_disjoint (mul_le_mul_of_nonneg_left
      (relativeMassBefore_add_mass_le_of_lt cuts h) hmu)).symm

theorem probabilityIntervals_card_le_population {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) {I : Finset (Fin K)} (S : Finset (WordOn k I))
    {mu : ℝ} (hmu : 0 ≤ mu) (hmuN : mu ≤ N) :
    (S.biUnion fun x => integerHalfOpen (mu*relativeMassBefore cuts x)
      (mu*(relativeMassBefore cuts x+massOn cuts x))).card ≤ N := by
  have hsub : (S.biUnion fun x => integerHalfOpen (mu*relativeMassBefore cuts x)
      (mu*(relativeMassBefore cuts x+massOn cuts x))) ⊆ Finset.Ico (0 : ℤ) (N : ℤ) := by
    intro z hz
    obtain ⟨x, _, hz⟩ := Finset.mem_biUnion.mp hz
    have hz := (mem_integerHalfOpen _ _ _).mp hz
    have hz0 : 0 ≤ (z : ℝ) := (mul_nonneg hmu (relativeMassBefore_nonnegative cuts x)).trans hz.1
    have htop := (mul_le_mul_of_nonneg_left
      (relativeMassBefore_add_mass_le_one cuts hN x) hmu).trans_eq (mul_one mu)
    have hzN : (z : ℝ) < N := hz.2.trans_le (htop.trans hmuN)
    exact Finset.mem_Ico.mpr ⟨by exact_mod_cast hz0, by exact_mod_cast hzN⟩
  exact (Finset.card_le_card hsub).trans_eq (by simp [Int.card_Ico])

theorem probabilityIntervals_card_bounds {k N K : ℕ} (cuts : Cuts k N K)
    {I : Finset (Fin K)} (S : Finset (WordOn k I)) {mu Q : ℝ}
    (hmu : 0 ≤ mu)
    (hmass : ∀ x ∈ S, Real.exp (-1)*Q ≤ mu*massOn cuts x ∧ mu*massOn cuts x ≤ Q) :
    (S.card : ℝ)*(Real.exp (-1)*Q-1) ≤
      ((S.biUnion fun x => integerHalfOpen (mu*relativeMassBefore cuts x)
        (mu*(relativeMassBefore cuts x+massOn cuts x))).card : ℝ) ∧
    ((S.biUnion fun x => integerHalfOpen (mu*relativeMassBefore cuts x)
      (mu*(relativeMassBefore cuts x+massOn cuts x))).card : ℝ) ≤ S.card*(Q+1) := by
  have hh := intervalUnion_card_bounds S (fun x => mu*relativeMassBefore cuts x)
    (fun x => mu*(relativeMassBefore cuts x+massOn cuts x))
    (fun x _ => by nlinarith [massOn_nonnegative cuts x])
    (probabilityIntervals_pairwiseDisjoint cuts S hmu)
  have hlow : (S.card : ℝ)*(Real.exp (-1)*Q) ≤ ∑ x ∈ S, mu*massOn cuts x := by
    simpa using Finset.sum_le_sum (fun x hx => (hmass x hx).1)
  have hupp : (∑ x ∈ S, mu*massOn cuts x) ≤ (S.card : ℝ)*Q := by
    simpa using Finset.sum_le_sum (fun x hx => (hmass x hx).2)
  have hid : (∑ x ∈ S, (mu*(relativeMassBefore cuts x+massOn cuts x)-
      mu*relativeMassBefore cuts x)) = ∑ x ∈ S, mu*massOn cuts x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hid] at hh
  constructor <;> nlinarith [hh.1, hh.2]

end RiffleLowerV2.Localization
