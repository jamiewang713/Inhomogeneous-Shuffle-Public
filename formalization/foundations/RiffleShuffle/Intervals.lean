import RiffleShuffle.Profiles
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Set.Basic

/-! Finite half-open lexicographic intervals, frozen items I01–I12. -/

noncomputable section
open scoped BigOperators

namespace RiffleShuffle
namespace WeightedLex

variable {α : Type*} [Fintype α] [LinearOrder α]

def left (w : α → ℝ) (a : α) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b => b < a), w b

def right (w : α → ℝ) (a : α) : ℝ := left w a + w a

def interval (w : α → ℝ) (a : α) : Set ℝ := Set.Ico (left w a) (right w a)

/-- I01. -/
theorem left_nonneg (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (a : α) :
    0 ≤ left w a :=
  Finset.sum_nonneg fun b _ => hw b

/-- I02. -/
theorem left_le_right (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (a : α) :
    left w a ≤ right w a := by
  unfold right
  exact le_add_of_nonneg_right (hw a)

/-- I03. -/
theorem right_le_one (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hsum : ∑ a, w a = 1) (a : α) : right w a ≤ 1 := by
  classical
  have hfilter : Finset.univ.filter (fun b : α => b ≤ a) =
      insert a (Finset.univ.filter (fun b : α => b < a)) := by
    ext b
    simp [le_iff_lt_or_eq, eq_comm, or_comm]
  have hright : right w a = ∑ b ∈ Finset.univ.filter (fun b => b ≤ a), w b := by
    rw [hfilter, Finset.sum_insert (by simp)]
    simp only [right, left, add_comm]
  calc
    right w a = ∑ b ∈ Finset.univ.filter (fun b => b ≤ a), w b := hright
    _ ≤ ∑ b, w b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun b _ _ => hw b)
    _ = 1 := hsum

/-- I04. -/
theorem right_le_left (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    {a b : α} (hab : a < b) : right w a ≤ left w b := by
  classical
  have hmem : a ∉ Finset.univ.filter (fun c : α => c < a) := by simp
  have hsubset : insert a (Finset.univ.filter (fun c : α => c < a)) ⊆
      Finset.univ.filter (fun c : α => c < b) := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simp [hab]
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_trans (Finset.mem_filter.mp hc).2 hab⟩
  calc
    right w a = ∑ c ∈ insert a (Finset.univ.filter (fun c : α => c < a)), w c := by
      rw [Finset.sum_insert hmem]
      simp only [right, left, add_comm]
    _ ≤ left w b := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun c _ _ => hw c)

/-- I05. -/
theorem weighted_intervals_disjoint (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    {a b : α} (hab : a ≠ b) : Disjoint (interval w a) (interval w b) := by
  apply Set.disjoint_left.mpr
  intro t ha hb
  change left w a ≤ t ∧ t < right w a at ha
  change left w b ≤ t ∧ t < right w b at hb
  rcases lt_or_gt_of_ne hab with hab | hba
  · have h := right_le_left w hw hab
    linarith
  · have h := right_le_left w hw hba
    linarith

/-- I06. -/
theorem weighted_interval_empty_iff (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (a : α) :
    interval w a = ∅ ↔ w a = 0 := by
  rw [interval, Set.Ico_eq_empty_iff]
  unfold right
  constructor
  · intro h
    have hnonneg := hw a
    linarith
  · intro h
    simp [h]

/-- I07. -/
theorem weighted_interval_length (w : α → ℝ) (a : α) :
    right w a - left w a = w a := by
  simp [right]

/-- I08. -/
theorem weighted_intervals_cover (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hsum : ∑ a, w a = 1) : (⋃ a, interval w a) = Set.Ico 0 1 := by
  classical
  have hright : ∀ a, right w a = ∑ b ∈ Finset.univ.filter (fun b => b ≤ a), w b := by
    intro a
    have hfilter : Finset.univ.filter (fun b : α => b ≤ a) =
        insert a (Finset.univ.filter (fun b : α => b < a)) := by
      ext b
      simp [le_iff_lt_or_eq, eq_comm, or_comm]
    rw [hfilter, Finset.sum_insert (by simp)]
    simp only [right, left, add_comm]
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ht
    change left w a ≤ t ∧ t < right w a at ha
    exact ⟨le_trans (left_nonneg w hw a) ha.1,
      lt_of_lt_of_le ha.2 (right_le_one w hw hsum a)⟩
  · intro ht
    have hall : (Finset.univ : Finset α).Nonempty := by
      by_contra h
      have he : (Finset.univ : Finset α) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hzero : ∑ a, w a = 0 := by rw [he]; simp
      linarith
    let z : α := Finset.univ.max' hall
    have hz : right w z = 1 := by
      rw [hright]
      have hfilter : Finset.univ.filter (fun b : α => b ≤ z) = Finset.univ := by
        apply Finset.filter_eq_self.mpr
        intro b hb
        exact Finset.le_max' _ _ hb
      rw [hfilter, hsum]
    let crossing : Finset α := Finset.univ.filter (fun a => t < right w a)
    have hc : crossing.Nonempty := by
      refine ⟨z, ?_⟩
      simp [crossing, hz, ht.2]
    let a : α := crossing.min' hc
    have ha : t < right w a := (Finset.mem_filter.mp (Finset.min'_mem crossing hc)).2
    have hleft : left w a ≤ t := by
      let lower : Finset α := Finset.univ.filter (fun b => b < a)
      by_cases hl : lower.Nonempty
      · let b : α := lower.max' hl
        have hba : b < a := (Finset.mem_filter.mp (Finset.max'_mem lower hl)).2
        have hbmax : ∀ c, c < a → c ≤ b := by
          intro c hca
          exact Finset.le_max' lower c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca⟩)
        have he : left w a = right w b := by
          rw [hright]
          unfold left
          congr 1
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hbmax c, fun hcb => lt_of_le_of_lt hcb hba⟩
        rw [he]
        by_contra h
        have hbc : b ∈ crossing := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, lt_of_not_ge h⟩
        have hab : a ≤ b := Finset.min'_le crossing b hbc
        exact (not_le_of_gt hba) hab
      · have he : lower = ∅ := Finset.not_nonempty_iff_eq_empty.mp hl
        have hz : left w a = 0 := by
          change ∑ b ∈ lower, w b = 0
          rw [he]
          simp
        rw [hz]
        exact ht.1
    exact Set.mem_iUnion.mpr ⟨a, hleft, ha⟩

end WeightedLex

def wordInterval {N k K m : ℕ} (P : PileProfile N k K) (x : Word k m) : Set ℝ :=
  WeightedLex.interval (mass P) x

def latticeInterval {N k K m : ℕ} (P : PileProfile N k K) (x : Word k m) : Set ℤ :=
  {z | ∃ t ∈ wordInterval P x, (z : ℝ) = (N : ℝ) * t}

def lexOpen {k m : ℕ} (a b : Word k m) : Set (Word k m) :=
  {x | a < x ∧ x < b}

/-- I09. -/
theorem word_interval_empty_iff {N k K m : ℕ} (P : PileProfile N k K)
    (x : Word k m) (hm : m ≤ K) : wordInterval P x = ∅ ↔ ¬ Legal P x := by
  rw [wordInterval, WeightedLex.weighted_interval_empty_iff (mass P) (mass_nonneg P)]
  constructor
  · intro hx hlegal
    have hpos := (mass_pos_iff_legal P x hm).mpr hlegal
    linarith
  · intro hnot
    apply le_antisymm
    · exact le_of_not_gt (fun hpos => hnot ((mass_pos_iff_legal P x hm).mp hpos))
    · exact mass_nonneg P x

/-- I10. -/
theorem word_intervals_disjoint {N k K m : ℕ} (P : PileProfile N k K)
    {x y : Word k m} (hxy : x ≠ y) : Disjoint (wordInterval P x) (wordInterval P y) :=
  WeightedLex.weighted_intervals_disjoint (mass P) (mass_nonneg P) hxy

/-- I11. -/
theorem word_intervals_cover {N k K m : ℕ} (P : PileProfile N k K) (hm : m ≤ K) :
    (⋃ x : Word k m, wordInterval P x) = Set.Ico 0 1 :=
  WeightedLex.weighted_intervals_cover (mass P) (mass_nonneg P) (mass_sum P hm)

/-- I12. -/
theorem lexOpen_convex {k m : ℕ} {a b y z t : Word k m}
    (hy : y ∈ lexOpen a b) (hz : z ∈ lexOpen a b) (hyt : y ≤ t) (htz : t ≤ z) :
    t ∈ lexOpen a b :=
  ⟨lt_of_lt_of_le hy.1 hyt, lt_of_le_of_lt htz hz.2⟩

end RiffleShuffle
