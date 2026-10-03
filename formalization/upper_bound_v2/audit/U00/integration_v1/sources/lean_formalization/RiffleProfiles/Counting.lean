import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

/-!
Finite counting statements F16, F17, and F19 from the frozen finite contract.
These are estimates of finite descriptors, without an asserted map from the
paper's boundary prefixes or a stochastic shuffle-model bridge.
-/

open scoped BigOperators

namespace RiffleProfiles

/-- Number of choices of at most `h` positions, each carrying one of `k` labels. -/
def lowCount (K h k : ℕ) : ℕ :=
  ∑ q ∈ (Finset.range (K + 1)).filter (fun q => q ≤ h), K.choose q * k ^ q

/-- The weighted binomial upper tail; it is zero when `h > K`. -/
noncomputable def tailWeight (K h : ℕ) (a : ℝ) : ℝ :=
  ∑ q ∈ (Finset.range (K + 1)).filter (fun q => h ≤ q), (K.choose q : ℝ) * a ^ q

private theorem sum_choose_mul_pow (K : ℕ) (a : ℝ) :
    (∑ q ∈ Finset.range (K + 1), (K.choose q : ℝ) * a ^ q) = (1 + a) ^ K := by
  simpa [mul_comm, add_comm] using (add_pow a 1 K).symm

/-- F16: a weighted upper tail is bounded by its generating function. -/
theorem tailWeight_le (K h : ℕ) {a z : ℝ} (ha : 0 ≤ a) (hz : 1 ≤ z) :
    tailWeight K h a ≤ (1 + a * z) ^ K / z ^ h := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  apply (le_div_iff₀ (pow_pos hz0 h)).2
  calc
    tailWeight K h a * z ^ h =
        ∑ q ∈ (Finset.range (K + 1)).filter (fun q => h ≤ q),
          ((K.choose q : ℝ) * a ^ q) * z ^ h := by
      rw [tailWeight, Finset.sum_mul]
    _ ≤ ∑ q ∈ (Finset.range (K + 1)).filter (fun q => h ≤ q),
          (K.choose q : ℝ) * (a * z) ^ q := by
      apply Finset.sum_le_sum
      intro q hq
      have hp : z ^ h ≤ z ^ q := pow_le_pow_right₀ hz (Finset.mem_filter.mp hq).2
      calc
        ((K.choose q : ℝ) * a ^ q) * z ^ h ≤
            ((K.choose q : ℝ) * a ^ q) * z ^ q :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha _))
        _ = (K.choose q : ℝ) * (a * z) ^ q := by rw [mul_pow]; ring
    _ ≤ ∑ q ∈ Finset.range (K + 1), (K.choose q : ℝ) * (a * z) ^ q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro q _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg ha hz0.le) _)
    _ = (1 + a * z) ^ K := sum_choose_mul_pow K (a * z)

/-- F17: a lower partial count is bounded by its generating function. -/
theorem lowCount_le (K h k : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    (lowCount K h k : ℝ) ≤ (1 + (k : ℝ) * z) ^ K / z ^ h := by
  apply (le_div_iff₀ (pow_pos hz0 h)).2
  calc
    (lowCount K h k : ℝ) * z ^ h =
        ∑ q ∈ (Finset.range (K + 1)).filter (fun q => q ≤ h),
          ((K.choose q : ℝ) * (k : ℝ) ^ q) * z ^ h := by
      simp only [lowCount, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Finset.sum_mul]
    _ ≤ ∑ q ∈ (Finset.range (K + 1)).filter (fun q => q ≤ h),
          (K.choose q : ℝ) * ((k : ℝ) * z) ^ q := by
      apply Finset.sum_le_sum
      intro q hq
      have hp : z ^ h ≤ z ^ q :=
        pow_le_pow_of_le_one hz0.le hz1 (Finset.mem_filter.mp hq).2
      calc
        ((K.choose q : ℝ) * (k : ℝ) ^ q) * z ^ h ≤
            ((K.choose q : ℝ) * (k : ℝ) ^ q) * z ^ q :=
          mul_le_mul_of_nonneg_left hp
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
        _ = (K.choose q : ℝ) * ((k : ℝ) * z) ^ q := by rw [mul_pow]; ring
    _ ≤ ∑ q ∈ Finset.range (K + 1),
          (K.choose q : ℝ) * ((k : ℝ) * z) ^ q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro q _ _
      exact mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hz0.le) _)
    _ = (1 + (k : ℝ) * z) ^ K := sum_choose_mul_pow K ((k : ℝ) * z)

/-- A set of at most `h` positions, with a digit at each selected position. -/
def SparsePattern (K h k : ℕ) :=
  Σ s : {s : Finset (Fin K) // s.card ≤ h}, (s.val → Fin k)

instance (K h k : ℕ) : Fintype (SparsePattern K h k) := by
  unfold SparsePattern
  infer_instance

/-- Forget the exceptional digits while retaining the exceptional positions. -/
def sparsePatternForget (K h k : ℕ) (p : SparsePattern K h k) : Finset (Fin K) :=
  p.1.val

/-- F19: the exact count of labelled sparse patterns. -/
theorem sparsePattern_card (K h k : ℕ) :
    Fintype.card (SparsePattern K h k) = lowCount K h k := by
  classical
  calc
    Fintype.card (SparsePattern K h k) =
        ∑ s : {s : Finset (Fin K) // s.card ≤ h}, k ^ s.val.card := by
      simp only [SparsePattern, Fintype.card_sigma, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe]
    _ = ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))).filter (fun s => s.card ≤ h),
          k ^ s.card := by
      exact (Finset.sum_subtype _ (by simp) (fun s : Finset (Fin K) => k ^ s.card)).symm
    _ = ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))),
          if s.card ≤ h then k ^ s.card else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ s ∈ (Finset.univ : Finset (Fin K)).powerset,
          if s.card ≤ h then k ^ s.card else 0 := by
      rw [Finset.powerset_univ]
    _ = ∑ q ∈ Finset.range (K + 1),
          ∑ s ∈ (Finset.univ : Finset (Fin K)).powersetCard q,
            if s.card ≤ h then k ^ s.card else 0 := by
      rw [Finset.sum_powerset]
      simp only [Finset.card_univ, Fintype.card_fin]
    _ = ∑ q ∈ Finset.range (K + 1),
          if q ≤ h then K.choose q * k ^ q else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      simpa [mul_ite] using
        (Finset.sum_powersetCard q (Finset.univ : Finset (Fin K))
          (fun n => if n ≤ h then k ^ n else 0))
    _ = lowCount K h k := by
      rw [lowCount, Finset.sum_filter]

/-- F19: forgetting labels cannot increase the number of descriptions. -/
theorem sparsePattern_forget_image_card_le (K h k : ℕ) :
    (Finset.univ.image (sparsePatternForget K h k)).card ≤ lowCount K h k := by
  classical
  calc
    (Finset.univ.image (sparsePatternForget K h k)).card ≤
        (Finset.univ : Finset (SparsePattern K h k)).card := Finset.card_image_le
    _ = lowCount K h k := by rw [Finset.card_univ, sparsePattern_card]

/-- A finite boundary description. Positions are zero based; the stopping
length is the number of positions. Deviations precede the final digit.
An empty extension uses digit zero as its fixed default. -/
def BoundaryDescriptor (K h k : ℕ) :=
  {d : Fin (K + 1) × Fin k × SparsePattern K h k //
    (∀ j ∈ d.2.2.1.val, j.val + 1 < d.1.val) ∧
    (d.1.val = 0 → d.2.1.val = 0)}

noncomputable instance (K h k : ℕ) : Fintype (BoundaryDescriptor K h k) := by
  classical
  unfold BoundaryDescriptor
  infer_instance

/-- F19: the boundary-description count, with the frozen source alphabet domain. -/
theorem boundaryDescriptor_card_le (K h k : ℕ) (_hk : 2 ≤ k) :
    Fintype.card (BoundaryDescriptor K h k) ≤ k * (K + 1) * lowCount K h k := by
  classical
  calc
    Fintype.card (BoundaryDescriptor K h k) ≤
        Fintype.card (Fin (K + 1) × Fin k × SparsePattern K h k) :=
      Fintype.card_subtype_le _
    _ = k * (K + 1) * lowCount K h k := by
      simp only [Fintype.card_prod, Fintype.card_fin, sparsePattern_card]
      ring

/-- Two boundary descriptions, labelled exceptional positions, and a finite
array of unnormalized good-digit counts. This is a refined descriptor space. -/
def ProfileDescriptor (K h_b h_e k D : ℕ) :=
  BoundaryDescriptor K h_b k × BoundaryDescriptor K h_b k ×
    SparsePattern K h_e k × (Fin D → Fin (K + 1))

noncomputable instance (K h_b h_e k D : ℕ) : Fintype (ProfileDescriptor K h_b h_e k D) := by
  unfold ProfileDescriptor
  infer_instance

/-- F19: the complete finite bound before converting powers of `log N` to
subpolynomial powers of `N`. -/
theorem profileDescriptor_card_le (K h_b h_e k D : ℕ) (hk : 2 ≤ k) :
    Fintype.card (ProfileDescriptor K h_b h_e k D) ≤
      k ^ 2 * (K + 1) ^ (D + 2) * lowCount K h_b k ^ 2 * lowCount K h_e k := by
  classical
  have hb := boundaryDescriptor_card_le K h_b k hk
  calc
    Fintype.card (ProfileDescriptor K h_b h_e k D) =
        Fintype.card (BoundaryDescriptor K h_b k) *
          (Fintype.card (BoundaryDescriptor K h_b k) *
            (lowCount K h_e k * (K + 1) ^ D)) := by
      simp only [ProfileDescriptor, Fintype.card_prod, sparsePattern_card,
        Fintype.card_fun, Fintype.card_fin]
    _ ≤ (k * (K + 1) * lowCount K h_b k) *
          ((k * (K + 1) * lowCount K h_b k) *
            (lowCount K h_e k * (K + 1) ^ D)) :=
      Nat.mul_le_mul hb (Nat.mul_le_mul_right _ hb)
    _ = k ^ 2 * (K + 1) ^ (D + 2) * lowCount K h_b k ^ 2 * lowCount K h_e k := by
      rw [pow_add]
      ring

end RiffleProfiles
