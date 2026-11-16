import RiffleLowerV2.Localization.Endpoints.ProductWeights

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization
open TimeProfile

theorem prefixMass_sidePrefix {k N K l m : ℕ} (cuts : Cuts k N K)
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K)
    (x : WordOn k (columnSet K l m)) (j : columnSet K l m) (d : Fin k) :
    prefixMass cuts (sidePrefix a l m x j d) =
      prefixMass cuts (prefixAt l a) *
        sideWeight (fun h : columnSet K l m => fun e => (cuts.count h.val e : ℝ)/N) x j d := by
  have hjl : l ≤ j.val.val := (Finset.mem_filter.mp j.property).2.1
  have hjm : j.val.val < m := (Finset.mem_filter.mp j.property).2.2
  have hjK : j.val.val+1 ≤ K := by omega
  unfold sidePrefix
  rw [prefixMass_prefixAt_eq_prod cuts _ _ hjK,
    prefixMass_prefixAt_eq_prod cuts l a (hlm.trans hm)]
  unfold sideWeight
  rw [← prod_subtype_dite (columnSet K l m)]
  simp only [columnSet, Finset.prod_filter, Nat.zero_le, true_and]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  simp only [List.Vector.get_ofFn]
  by_cases hhl : h.val < l
  · have hhj : h ≠ j.val := fun he => by have := congrArg Fin.val he; omega
    have hhI : ¬(l ≤ h.val ∧ h.val < m) := by omega
    have hhs : h.val < j.val.val+1 := by omega
    simp [hhl, hhj, hhI, hhs]
  · by_cases hhI : l ≤ h.val ∧ h.val < m
    · have hmem : h ∈ columnSet K l m := by simpa [columnSet] using hhI
      by_cases hhj : h = j.val
      · subst h
        simp [hhl, columnSet]
      · have hsub : (⟨h, hmem⟩ : columnSet K l m) ≠ j := fun he => hhj (congrArg Subtype.val he)
        have horder : (⟨h, hmem⟩ : columnSet K l m) ≤ j ↔ h.val < j.val.val+1 := by
          change h.val ≤ j.val.val ↔ h.val < j.val.val+1
          omega
        simp [hhl, hhI, hhj, hsub, horder, columnSet]
    · have hhs : ¬h.val < j.val.val+1 := by omega
      simp [hhl, hhI, hhs]

theorem prefixMean_sidePrefix {k N K l m : ℕ} (cuts : Cuts k N K)
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K)
    (x : WordOn k (columnSet K l m)) (j : columnSet K l m) (d : Fin k) :
    prefixMean cuts (sidePrefix a l m x j d) =
      prefixMean cuts (prefixAt l a) *
        sideWeight (fun h : columnSet K l m => fun e => (cuts.count h.val e : ℝ)/N) x j d := by
  simp only [prefixMean, prefixMass_sidePrefix cuts a hlm hm x j d]
  ring

theorem count_fraction_sum {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (j : Fin K) :
    (∑ d : Fin k, (cuts.count j d : ℝ)/N) = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, cuts.sum_count]
  exact div_self (by exact_mod_cast Nat.ne_of_gt hN)

theorem massOn_sum {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (I : Finset (Fin K)) : (∑ y : WordOn k I, massOn cuts y) = 1 := by
  unfold massOn
  rw [← Fintype.prod_sum (fun (j : I) (d : Fin k) => (cuts.count j.val d : ℝ)/N)]
  simp_rw [count_fraction_sum cuts hN]
  simp

def relativeMassAfter {k N K : ℕ} (cuts : Cuts k N K) {I : Finset (Fin K)}
    (x : WordOn k I) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : WordOn k I => wordOnList x < wordOnList y), massOn cuts y

theorem sideWeight_eq_massOn_sum {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {I : Finset (Fin K)} (x : WordOn k I) (j : I) (d : Fin k) :
    sideWeight (fun h : I => fun e => (cuts.count h.val e : ℝ)/N) x j d =
      ∑ y : WordOn k I, if sideMatch x y j d then massOn cuts y else 0 := by
  have hs := sideWeight_eq_sum
    (fun h : I => fun e => (cuts.count h.val e : ℝ)/N)
    (fun h => count_fraction_sum cuts hN h.val) x j d
  convert hs using 1
  apply Finset.sum_congr
  · ext y
    simp
  · intro y _
    rfl

theorem relativeMassBefore_eq_sideWeight {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) {I : Finset (Fin K)} (x : WordOn k I) :
    relativeMassBefore cuts x =
      ∑ j : I, ∑ d ∈ Finset.univ.filter (fun d : Fin k => d < x j),
        sideWeight (fun h : I => fun e => (cuts.count h.val e : ℝ)/N) x j d := by
  have hs := weighted_side_partition x (fun y : WordOn k I => y) (fun _ => True)
    (massOn cuts) (fun d e : Fin k => d < e) (fun _ _ h => ne_of_lt h)
  simp only [true_and] at hs
  simp_rw [← wordOnList_lt_iff] at hs
  simp_rw [← sideWeight_eq_massOn_sum cuts hN] at hs
  simp only [relativeMassBefore, Finset.sum_filter] at hs ⊢
  convert hs using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr
  · ext d
    simp
  · intros
    split_ifs <;> rfl

theorem relativeMassAfter_eq_sideWeight {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) {I : Finset (Fin K)} (x : WordOn k I) :
    relativeMassAfter cuts x =
      ∑ j : I, ∑ d ∈ Finset.univ.filter (fun d : Fin k => x j < d),
        sideWeight (fun h : I => fun e => (cuts.count h.val e : ℝ)/N) x j d := by
  have hs := weighted_side_partition x (fun y : WordOn k I => y) (fun _ => True)
    (massOn cuts) (fun d e : Fin k => e < d) (fun _ _ h => ne_of_gt h)
  have horder (y : WordOn k I) :
      (∃ j, x j < y j ∧ ∀ h, h < j → y h = x h) ↔ wordOnList x < wordOnList y := by
    rw [wordOnList_lt_iff]
    constructor <;> rintro ⟨j, hj, hpre⟩ <;>
      exact ⟨j, hj, fun h hh => (hpre h hh).symm⟩
  simp only [true_and] at hs
  simp_rw [horder, ← sideWeight_eq_massOn_sum cuts hN] at hs
  simp only [relativeMassAfter, Finset.sum_filter] at hs ⊢
  convert hs using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr
  · ext d
    simp
  · intros
    split_ifs <;> rfl

theorem relativeMass_total {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {I : Finset (Fin K)} (x : WordOn k I) :
    relativeMassBefore cuts x + massOn cuts x + relativeMassAfter cuts x = 1 := by
  have hsingle : massOn cuts x = ∑ y : WordOn k I, if y = x then massOn cuts y else 0 := by simp
  rw [hsingle, relativeMassBefore, relativeMassAfter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← massOn_sum cuts hN I]
  apply Finset.sum_congr rfl
  intro y _
  rcases lt_trichotomy (wordOnList y) (wordOnList x) with h | h | h
  · have hne : y ≠ x := fun he => (ne_of_lt h) (congrArg wordOnList he)
    simp [h, hne, not_lt_of_gt h]
  · have he : y = x := wordOnList_injective h
    simp [he]
  · have hne : y ≠ x := fun he => (ne_of_gt h) (congrArg wordOnList he)
    simp [h, hne, not_lt_of_gt h]

theorem sideMean_sum_le {k N K l m : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (a : Word k K) (hlm : l ≤ m) (hm : m ≤ K) (x : WordOn k (columnSet K l m))
    (R : Fin k → Fin k → Prop) (hR : ∀ d e, R d e → d ≠ e) :
    (∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d => R d (x j)),
      prefixMean cuts (sidePrefix a l m x j d)) ≤ prefixMean cuts (prefixAt l a) := by
  simp_rw [prefixMean_sidePrefix cuts a hlm hm x]
  simp_rw [← Finset.mul_sum]
  have hp0 : 0 ≤ prefixMean cuts (prefixAt l a) := by
    unfold prefixMean prefixMass
    positivity
  have hs := sum_sideWeight_le_one
    (fun j : columnSet K l m => fun d => (cuts.count j.val d : ℝ)/N)
    (fun j => count_fraction_sum cuts hN j.val) (fun _ _ => by positivity) x R hR
  simpa using mul_le_mul_of_nonneg_left hs hp0

end RiffleLowerV2.Localization
