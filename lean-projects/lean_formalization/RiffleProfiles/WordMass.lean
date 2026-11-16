import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import RiffleProfiles.Counting

/-! Finite word-mass and coarse-fibre estimates from frozen F18 and F20.
No probability-space or shuffle expectation identification is made here. -/

namespace RiffleProfiles

open scoped BigOperators

section WordMass

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α]

/-- The product weight of a finite word. -/
def wordWeight (p : ι → α → ℝ) (x : ι → α) : ℝ :=
  ∏ j, p j (x j)

/-- Positions whose selected digit belongs to the prescribed bad set. -/
def badPositions (bad : ι → Finset α) (x : ι → α) : Finset ι :=
  Finset.univ.filter fun j => x j ∈ bad j

/-- The number of bad positions of a word. -/
def badCount (bad : ι → Finset α) (x : ι → α) : ℕ :=
  (badPositions bad x).card

/-- Total product weight of words with at least `h` bad positions. -/
def badWordMass (p : ι → α → ℝ) (bad : ι → Finset α) (h : ℕ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : ι → α => h ≤ badCount bad x), wordWeight p x

omit [DecidableEq ι] [Fintype α] [DecidableEq α] in
theorem wordWeight_nonneg (p : ι → α → ℝ)
    (hp : ∀ j a, 0 ≤ p j a) (x : ι → α) : 0 ≤ wordWeight p x := by
  exact Finset.prod_nonneg fun j _ => hp j (x j)

omit [DecidableEq α] in
theorem wordWeight_sum (p : ι → α → ℝ)
    (hp : ∀ j, ∑ a, p j a = 1) : ∑ x : ι → α, wordWeight p x = 1 := by
  unfold wordWeight
  rw [← Fintype.prod_sum]
  simp [hp]

omit [DecidableEq ι] [Fintype α] in
theorem badCount_generating_product (bad : ι → Finset α) (x : ι → α) (z : ℝ) :
    z ^ badCount bad x = ∏ j, if x j ∈ bad j then z else 1 := by
  simp [badCount, badPositions, Finset.prod_ite]

theorem wordWeight_generating (p : ι → α → ℝ) (bad : ι → Finset α) (z : ℝ) :
    ∑ x : ι → α, wordWeight p x * z ^ badCount bad x =
      ∏ j, ∑ a, p j a * (if a ∈ bad j then z else 1) := by
  simp_rw [badCount_generating_product, wordWeight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (j : ι) (a : α) =>
    p j a * (if a ∈ bad j then z else 1))).symm

omit [Fintype ι] [DecidableEq ι] in
theorem coordinate_generating (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j, ∑ a, p j a = 1) (j : ι) (z : ℝ) :
    (∑ a, p j a * (if a ∈ bad j then z else 1)) =
      1 + (∑ a ∈ bad j, p j a) * (z - 1) := by
  have hterm (a : α) : p j a * (if a ∈ bad j then z else 1) =
      p j a + (if a ∈ bad j then p j a else 0) * (z - 1) := by
    split_ifs <;> ring
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, ← Finset.sum_mul, hp, Finset.sum_ite]

theorem wordWeight_generating_le (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j a, 0 ≤ p j a) (hnorm : ∀ j, ∑ a, p j a = 1)
    {a z : ℝ} (hbad : ∀ j, (∑ d ∈ bad j, p j d) ≤ a) (hz : 1 ≤ z) :
    (∑ x : ι → α, wordWeight p x * z ^ badCount bad x) ≤
      (1 + a * (z - 1)) ^ Fintype.card ι := by
  rw [wordWeight_generating]
  simp_rw [coordinate_generating p bad hnorm]
  have hz' : 0 ≤ z - 1 := sub_nonneg.mpr hz
  calc
    (∏ j, (1 + (∑ d ∈ bad j, p j d) * (z - 1))) ≤
        ∏ _j : ι, (1 + a * (z - 1)) := by
      apply Finset.prod_le_prod
      · intro j _
        exact add_nonneg zero_le_one
          (mul_nonneg (Finset.sum_nonneg fun d _ => hp j d) hz')
      · intro j _
        exact add_le_add_left (mul_le_mul_of_nonneg_right (hbad j) hz') 1
    _ = _ := by simp

/-- F18: the finite product-weight bad-count bound. -/
theorem badWordMass_le (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j a, 0 ≤ p j a) (hnorm : ∀ j, ∑ a, p j a = 1)
    {a z : ℝ} (_ha : 0 ≤ a) (hbad : ∀ j, (∑ d ∈ bad j, p j d) ≤ a)
    (hz : 1 ≤ z) (h : ℕ) :
    badWordMass p bad h ≤ (1 + a * (z - 1)) ^ Fintype.card ι / z ^ h := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  apply (le_div_iff₀ (pow_pos hz0 h)).2
  unfold badWordMass
  rw [Finset.sum_mul]
  calc
    (∑ x ∈ Finset.univ.filter (fun x : ι → α => h ≤ badCount bad x),
        wordWeight p x * z ^ h) ≤
        ∑ x ∈ Finset.univ.filter (fun x : ι → α => h ≤ badCount bad x),
          wordWeight p x * z ^ badCount bad x := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hz (Finset.mem_filter.mp hx).2) (wordWeight_nonneg p hp x)
    _ ≤ ∑ x : ι → α, wordWeight p x * z ^ badCount bad x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x _ _
      exact mul_nonneg (wordWeight_nonneg p hp x) (pow_nonneg hz0.le _)
    _ ≤ _ := wordWeight_generating_le p bad hp hnorm hbad hz

omit [Fintype ι] [DecidableEq ι] [DecidableEq α] in
/-- A per-digit small-mass bound gives the bad-coordinate mass bound. -/
theorem badDigitMass_le (p : ι → α → ℝ) (bad : ι → Finset α)
    {χ : ℝ} (hχ : 0 < χ) (hsmall : ∀ j d, d ∈ bad j → p j d ≤ χ) (j : ι) :
    (∑ d ∈ bad j, p j d) ≤ (Fintype.card α : ℝ) * χ := by
  calc
    (∑ d ∈ bad j, p j d) ≤ ∑ _d ∈ bad j, χ := by
      exact Finset.sum_le_sum fun d hd => hsmall j d hd
    _ = ((bad j).card : ℝ) * χ := by simp
    _ ≤ (Fintype.card α : ℝ) * χ := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ _)) hχ.le

/-- F18 with every bad digit of mass at most `χ`. -/
theorem badWordMass_smallDigits_le (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j d, 0 ≤ p j d) (hnorm : ∀ j, ∑ d, p j d = 1)
    {χ z : ℝ} (hχ : 0 < χ) (hsmall : ∀ j d, d ∈ bad j → p j d ≤ χ)
    (hz : 1 ≤ z) (h : ℕ) :
    badWordMass p bad h ≤
      (1 + ((Fintype.card α : ℝ) * χ) * (z - 1)) ^ Fintype.card ι / z ^ h := by
  exact badWordMass_le p bad hp hnorm
    (mul_nonneg (Nat.cast_nonneg _) hχ.le) (badDigitMass_le p bad hχ hsmall) hz h

/-- This is multiplication of finite word mass, not an expectation identity. -/
theorem scaled_badWordMass_le (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j d, 0 ≤ p j d) (hnorm : ∀ j, ∑ d, p j d = 1)
    {a z : ℝ} (ha : 0 ≤ a) (hbad : ∀ j, (∑ d ∈ bad j, p j d) ≤ a)
    (hz : 1 ≤ z) (h N : ℕ) :
    (N : ℝ) * badWordMass p bad h ≤
      (N : ℝ) * ((1 + a * (z - 1)) ^ Fintype.card ι / z ^ h) := by
  exact mul_le_mul_of_nonneg_left (badWordMass_le p bad hp hnorm ha hbad hz h)
    (Nat.cast_nonneg N)

/-- Product weights restricted to one allowed-digit set at each position. -/
theorem box_word_mass (p : ι → α → ℝ) (allowed : ι → Finset α) :
    (∑ x ∈ Finset.univ.filter (fun x : ι → α => ∀ j, x j ∈ allowed j), wordWeight p x) =
      ∏ j, ∑ d ∈ allowed j, p j d := by
  calc
    (∑ x ∈ Finset.univ.filter (fun x : ι → α => ∀ j, x j ∈ allowed j), wordWeight p x) =
        ∑ x : ι → α, ∏ j, if x j ∈ allowed j then p j (x j) else 0 := by
      simp [Finset.sum_filter, Finset.prod_ite_zero, wordWeight]
    _ = ∏ j, ∑ d, if d ∈ allowed j then p j d else 0 := by
      exact (Fintype.prod_sum
        (fun (j : ι) (d : α) => if d ∈ allowed j then p j d else 0)).symm
    _ = _ := by simp [Finset.sum_ite]

/-- A fixed exact bad-position set has mass at most the product bad-mass bound. -/
theorem exact_badPositions_mass_le (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j d, 0 ≤ p j d) (hnorm : ∀ j, ∑ d, p j d = 1)
    {a : ℝ} (hbad : ∀ j, (∑ d ∈ bad j, p j d) ≤ a) (S : Finset ι) :
    (∑ x ∈ Finset.univ.filter (fun x : ι → α => badPositions bad x = S), wordWeight p x)
      ≤ a ^ S.card := by
  let allowed : ι → Finset α := fun j => if j ∈ S then bad j else (bad j)ᶜ
  have hiff (x : ι → α) : badPositions bad x = S ↔ ∀ j, x j ∈ allowed j := by
    simp only [badPositions, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'
    intro j
    by_cases hj : j ∈ S <;> simp [allowed, hj]
  calc
    (∑ x ∈ Finset.univ.filter (fun x : ι → α => badPositions bad x = S), wordWeight p x) =
        ∏ j, ∑ d ∈ allowed j, p j d := by
      simp_rw [hiff]
      exact box_word_mass p allowed
    _ ≤ ∏ j, if j ∈ S then a else 1 := by
      apply Finset.prod_le_prod
      · intro j _
        exact Finset.sum_nonneg fun d _ => hp j d
      · intro j _
        by_cases hj : j ∈ S
        · simpa [allowed, hj] using hbad j
        · simp only [allowed, hj, ↓reduceIte]
          calc
            (∑ d ∈ (bad j)ᶜ, p j d) ≤ ∑ d, p j d := by
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun d _ _ => hp j d)
            _ = 1 := hnorm j
    _ = a ^ S.card := by simp [Finset.prod_ite]

omit [DecidableEq ι] [Fintype α] [DecidableEq α] in
/-- Counting prescribed bad-position sets by their cardinality. -/
theorem sum_badSet_weights (a : ℝ) (h : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => h ≤ S.card), a ^ S.card) =
      tailWeight (Fintype.card ι) h a := by
  calc
    (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => h ≤ S.card), a ^ S.card) =
        ∑ S ∈ (Finset.univ : Finset ι).powerset,
          if h ≤ S.card then a ^ S.card else 0 := by
      rw [Finset.sum_filter, Finset.powerset_univ]
    _ = ∑ q ∈ Finset.range (Fintype.card ι + 1),
          ∑ S ∈ (Finset.univ : Finset ι).powersetCard q,
            if h ≤ S.card then a ^ S.card else 0 := by
      rw [Finset.sum_powerset]
      simp only [Finset.card_univ]
    _ = ∑ q ∈ Finset.range (Fintype.card ι + 1),
          if h ≤ q then (Nat.choose (Fintype.card ι) q : ℝ) * a ^ q else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      simpa [nsmul_eq_mul, mul_ite] using
        (Finset.sum_powersetCard q (Finset.univ : Finset ι)
          (fun n => if h ≤ n then a ^ n else 0))
    _ = _ := by rw [tailWeight, Finset.sum_filter]

/-- F18: the finite union-tail alternative, grouped by exact bad-position sets. -/
theorem badWordMass_le_tailWeight (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j d, 0 ≤ p j d) (hnorm : ∀ j, ∑ d, p j d = 1)
    {a : ℝ} (_ha : 0 ≤ a) (hbad : ∀ j, (∑ d ∈ bad j, p j d) ≤ a) (h : ℕ) :
    badWordMass p bad h ≤ tailWeight (Fintype.card ι) h a := by
  calc
    badWordMass p bad h =
        ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => h ≤ S.card),
          ∑ x ∈ Finset.univ.filter (fun x : ι → α => badPositions bad x = S),
            wordWeight p x := by
      symm
      simpa [badWordMass, badCount] using
        (Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (ι → α))
          ((Finset.univ : Finset (Finset ι)).filter (fun S => h ≤ S.card))
          (badPositions bad) (wordWeight p))
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => h ≤ S.card), a ^ S.card := by
      exact Finset.sum_le_sum fun S _ => exact_badPositions_mass_le p bad hp hnorm hbad S
    _ = _ := sum_badSet_weights a h

/-- The union-tail form with the source's per-digit small-mass input. -/
theorem badWordMass_smallDigits_le_tailWeight (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j d, 0 ≤ p j d) (hnorm : ∀ j, ∑ d, p j d = 1)
    {χ : ℝ} (hχ : 0 < χ) (hsmall : ∀ j d, d ∈ bad j → p j d ≤ χ) (h : ℕ) :
    badWordMass p bad h ≤ tailWeight (Fintype.card ι) h ((Fintype.card α : ℝ) * χ) := by
  exact badWordMass_le_tailWeight p bad hp hnorm
    (mul_nonneg (Nat.cast_nonneg _) hχ.le) (badDigitMass_le p bad hχ hsmall) h

/-- Multiplication of the union-tail bound, without a shuffle-model identification. -/
theorem scaled_badWordMass_le_tailWeight (p : ι → α → ℝ) (bad : ι → Finset α)
    (hp : ∀ j d, 0 ≤ p j d) (hnorm : ∀ j, ∑ d, p j d = 1)
    {a : ℝ} (ha : 0 ≤ a) (hbad : ∀ j, (∑ d ∈ bad j, p j d) ≤ a) (h N : ℕ) :
    (N : ℝ) * badWordMass p bad h ≤ (N : ℝ) * tailWeight (Fintype.card ι) h a := by
  exact mul_le_mul_of_nonneg_left (badWordMass_le_tailWeight p bad hp hnorm ha hbad h)
    (Nat.cast_nonneg N)

end WordMass

/-- The finite squared-edge bound used in F18. -/
theorem sum_edgeProbability_sq_le {β : Type*} (s : Finset β) (p : β → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    (∑ i ∈ s, p i ^ 2) ≤ ∑ i ∈ s, p i := by
  apply Finset.sum_le_sum
  intro i hi
  rw [pow_two]
  exact mul_le_of_le_one_right (hp0 i hi) (hp1 i hi)

section CoarseFibres

variable {β E : Type*} [Fintype E]

/-- F20: partition a coarse finite class by its exceptional labels. -/
theorem coarse_fibre_card_le (s : Finset β) (k B : ℕ) (labels : β → E → Fin k)
    (hfibre : ∀ lab : E → Fin k, (s.filter fun x => labels x = lab).card ≤ B) :
    s.card ≤ k ^ Fintype.card E * B := by
  classical
  calc
    s.card = ∑ lab : E → Fin k, (s.filter fun x => labels x = lab).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _lab : E → Fin k, B := Finset.sum_le_sum fun lab _ => hfibre lab
    _ = _ := by simp

end CoarseFibres

/-- F20 specialized to the actual restrictions of words to an exceptional set. -/
theorem coarse_word_fibre_card_le {ι : Type*} (k B : ℕ)
    (s : Finset (ι → Fin k)) (E : Finset ι)
    (hfibre : ∀ lab : E → Fin k,
      (s.filter fun x => (fun j : E => x j) = lab).card ≤ B) :
    s.card ≤ k ^ E.card * B := by
  classical
  simpa using coarse_fibre_card_le s k B (fun x (j : E) => x j) hfibre

section CoarseCollision

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

/-- The source coarse data specialized to a single time/simplex cell. -/
def oneCellCoarseProfile (good : ι → α → Bool) (x : ι → α) :
    (α → ℕ) × Finset ι :=
  ((fun a => (Finset.univ.filter fun j => good j (x j) = true ∧ x j = a).card),
    Finset.univ.filter fun j => good j (x j) = false)

/-- Two exceptional digits give distinct words with identical coarse data. -/
theorem coarseProfile_not_injective :
    ¬ Function.Injective
      (oneCellCoarseProfile (fun (_ : Fin 1) (_ : Fin 2) => false)) := by
  intro hinj
  have hsame : oneCellCoarseProfile (fun (_ : Fin 1) (_ : Fin 2) => false)
        (fun _ : Fin 1 => (0 : Fin 2)) =
      oneCellCoarseProfile (fun (_ : Fin 1) (_ : Fin 2) => false)
        (fun _ : Fin 1 => (1 : Fin 2)) := by
    simp [oneCellCoarseProfile]
  have hneq := congrFun (hinj hsame) (0 : Fin 1)
  norm_num at hneq

end CoarseCollision

end RiffleProfiles
