import RiffleLowerV2.Shared.Geometry

noncomputable section
open scoped BigOperators
open TimeProfile
namespace RiffleLowerV2.Types
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {Ω : Type*} [DecidableEq Ω]

/-- A finite fiber; the codomain includes indices whose fibers are empty. -/
def indexFiber (s : Finset Ω) (f : Ω → ℕ) (b : ℕ) : Finset Ω :=
  s.filter fun x => f x = b

lemma indexFiber_nonempty {s : Finset Ω} {f : Ω → ℕ} {b : ℕ} :
    (indexFiber s f b).Nonempty ↔ b ∈ s.image f := by
  simp only [indexFiber, Finset.filter_nonempty_iff, Finset.mem_image]

lemma exists_maximal_indexFiber (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) :
    ∃ b, ∀ a, (indexFiber s f a).card ≤ (indexFiber s f b).card := by
  obtain ⟨b, hb, hmax⟩ := (s.image f).exists_max_image
    (fun a => (indexFiber s f a).card) (hs.image f)
  refine ⟨b, fun a => ?_⟩
  by_cases ha : a ∈ s.image f
  · exact hmax a ha
  · have he : indexFiber s f a = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (mt indexFiber_nonempty.mp ha)
    simp [he]

/-- The smallest maximizing index is a deterministic choice. -/
def leastMaxBin (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) : ℕ :=
  Nat.find (exists_maximal_indexFiber s f hs)

lemma leastMaxBin_maximal (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) (b : ℕ) :
    (indexFiber s f b).card ≤ (indexFiber s f (leastMaxBin s f hs)).card :=
  Nat.find_spec (exists_maximal_indexFiber s f hs) b

lemma leastMaxBin_tie (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) (b : ℕ)
    (hb : (indexFiber s f b).card = (indexFiber s f (leastMaxBin s f hs)).card) :
    leastMaxBin s f hs ≤ b := by
  apply Nat.find_min'
  intro a
  rw [hb]
  exact leastMaxBin_maximal s f hs a

lemma leastMaxBin_nonempty (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) :
    (indexFiber s f (leastMaxBin s f hs)).Nonempty := by
  obtain ⟨x, hx⟩ := hs
  have hpos : 0 < (indexFiber s f (f x)).card :=
    Finset.card_pos.mpr (indexFiber_nonempty.mpr (Finset.mem_image_of_mem f hx))
  exact Finset.card_pos.mp (hpos.trans_le (leastMaxBin_maximal s f ⟨x, hx⟩ (f x)))

lemma leastMaxBin_card_bound (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) :
    s.card ≤ (indexFiber s f (leastMaxBin s f hs)).card * (s.image f).card := by
  exact Finset.card_le_mul_card_image s _ (fun b _ => leastMaxBin_maximal s f hs b)

lemma floor_image_card_bound (s : Finset Ω) (g : Ω → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hg : ∀ x ∈ s, g x ≤ M) :
    ((s.image fun x => ⌊g x⌋₊).card : ℝ) ≤ 2 + M := by
  have hsub : (s.image fun x => ⌊g x⌋₊) ⊆ Finset.range (⌊M⌋₊ + 1) := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (hg x hx)))
  have hc : (s.image fun x => ⌊g x⌋₊).card ≤ ⌊M⌋₊ + 1 := by
    simpa using Finset.card_le_card hsub
  have hcr : ((s.image fun x => ⌊g x⌋₊).card : ℝ) ≤ (⌊M⌋₊ : ℝ) + 1 := by
    exact_mod_cast hc
  have hf := Nat.floor_le hM
  linarith

lemma leastMaxBin_log_loss (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty)
    {B : ℝ} (hB : 0 < B) (hbins : ((s.image f).card : ℝ) ≤ B) :
    0 ≤ Real.log s.card - Real.log (indexFiber s f (leastMaxBin s f hs)).card ∧
    Real.log s.card - Real.log (indexFiber s f (leastMaxBin s f hs)).card ≤
      Real.log B := by
  let t := indexFiber s f (leastMaxBin s f hs)
  have ht : 0 < (t.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (leastMaxBin_nonempty s f hs)
  have hspos : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hsub : t ⊆ s := Finset.filter_subset _ _
  have hle : (t.card : ℝ) ≤ s.card := by exact_mod_cast Finset.card_le_card hsub
  have hprod : (s.card : ℝ) ≤ t.card * ((s.image f).card : ℝ) := by
    exact_mod_cast leastMaxBin_card_bound s f hs
  have hprod' : (s.card : ℝ) ≤ (t.card : ℝ) * B :=
    hprod.trans (mul_le_mul_of_nonneg_left hbins ht.le)
  have hlog := Real.log_le_log hspos hprod'
  rw [Real.log_mul ht.ne' hB.ne'] at hlog
  exact ⟨sub_nonneg.mpr (Real.log_le_log ht hle), by dsimp [t] at hlog; linarith⟩

lemma massOn_pos {k N K : ℕ} (cuts : Cuts k N K) {I : Finset (Fin K)}
    (x : WordOn k I) (h : ∀ j : I, 0 < (cuts.count j.val (x j) : ℝ) / N) :
    0 < massOn cuts x := Finset.prod_pos fun j _ => h j

lemma massOn_le_one {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {I : Finset (Fin K)} (x : WordOn k I) : massOn cuts x ≤ 1 := by
  apply Finset.prod_le_one
  · intro j _
    positivity
  · intro j _
    exact prob_le_one (cuts.profile hN j.val) (x j)

lemma massOn_cost_bounds {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {I : Finset (Fin K)} (x : WordOn k I) {xi : ℝ} (hxi : 0 < xi)
    (h : ∀ j : I, xi ≤ (cuts.count j.val (x j) : ℝ) / N) :
    0 ≤ -Real.log (massOn cuts x) ∧
      -Real.log (massOn cuts x) ≤ (I.card : ℝ) * Real.log (1 / xi) := by
  have hp (j : I) : 0 < (cuts.count j.val (x j) : ℝ) / N := hxi.trans_le (h j)
  have hm := massOn_pos cuts x hp
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos hm.le (massOn_le_one cuts hN x))
  · rw [massOn, Real.log_prod (s := Finset.univ) (f := fun j : I => (cuts.count j.val (x j) : ℝ) / N) (fun j _ => (hp j).ne'), ← Finset.sum_neg_distrib]
    calc
      (∑ j : I, -Real.log ((cuts.count j.val (x j) : ℝ) / N)) ≤
          ∑ _j : I, Real.log (1 / xi) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [one_div, Real.log_inv] using neg_le_neg (Real.log_le_log hxi (h j))
      _ = _ := by simp

lemma massBin_eq_indexFiber {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (hpos : ∀ x ∈ roundedClass cuts hN P I D, 0 < massOn cuts x) (b : ℕ) :
    massBin cuts hN P I D b = indexFiber (roundedClass cuts hN P I D)
      (fun x => ⌊-Real.log (massOn cuts x)⌋₊) b := by
  ext x
  simp only [massBin, indexFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hb⟩
    exact ⟨hx, (Nat.floor_eq_iff (neg_nonneg.mpr
      (Real.log_nonpos (hpos x hx).le (massOn_le_one cuts hN x)))).mpr hb⟩
  · rintro ⟨hx, hb⟩
    exact ⟨hx, (Nat.floor_eq_iff (neg_nonneg.mpr
      (Real.log_nonpos (hpos x hx).le (massOn_le_one cuts hN x)))).mp hb⟩

lemma card_eq_rpow_log_div (N n : ℕ) (hN : 2 ≤ N) (hn : 0 < n) :
    (n : ℝ) = (N : ℝ) ^ (Real.log n / logScale N) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hNr]
  have hL := (logScale_pos hN).ne'
  rw [show Real.log (N : ℝ) * (Real.log (n : ℝ) / logScale N) = Real.log n by
    dsimp [logScale] at *; field_simp]
  exact (Real.exp_log hnr).symm

lemma rpow_neg_typeJ {k : ℕ} {P : BorelPartition k} (N : ℕ) (hN : 2 ≤ N)
    (D : RoundedTypeData P) :
    (N : ℝ) ^ (-typeJ N D) = Real.exp (-(D.binIndex : ℝ)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  rw [Real.rpow_def_of_pos hNr]
  congr 1
  dsimp [typeJ, logScale]
  have hL := (logScale_pos hN).ne'
  dsimp [logScale] at hL
  field_simp

lemma selectedClass_exact_mass {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hN2 : 2 ≤ N) (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (hpos : ∀ x ∈ roundedClass cuts hN P I D, 0 < massOn cuts x) :
    ∀ x ∈ selectedClass cuts hN P I D,
      Real.exp (-1) * (N : ℝ)^(-typeJ N D) < massOn cuts x ∧
      massOn cuts x ≤ (N : ℝ)^(-typeJ N D) := by
  intro x hx
  obtain ⟨hx0, hlo, hhi⟩ := Finset.mem_filter.mp hx
  have hp := hpos x hx0
  rw [rpow_neg_typeJ N hN2 D, ← Real.exp_add]
  constructor
  · rw [← Real.exp_log hp, Real.exp_lt_exp]
    linarith
  · rw [← Real.exp_log hp, Real.exp_le_exp]
    linarith

lemma roundedClass_actual_lower {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    {xi C : ℝ} (hreg : P.IsRegular xi C)
    (hsupport : ∀ i l, prob (P.rep i) l ≤ 2*xi → D.count i l = 0) :
    ∀ x ∈ roundedClass cuts hN P I D, ∀ j : I,
      xi ≤ (cuts.count j.val (x j) : ℝ) / N := by
  intro x hx j
  have hcount := (Finset.mem_filter.mp hx).2
  let i := P.classify (cuts.profile hN j.val)
  have hj : 0 < wordCellCount cuts hN P x i (x j) := by
    apply Finset.card_pos.mpr
    exact ⟨j, by simp [i]⟩
  have hgood : 2*xi < prob (P.rep i) (x j) := by
    by_contra hh
    rw [hcount i (x j), hsupport i (x j) (le_of_not_gt hh)] at hj
    exact (Nat.lt_irrefl 0) hj
  exact (hreg.good_digit i (cuts.profile hN j.val) (x j) rfl hgood).1.le

/-- Change only the bin index of already chosen integer counts. -/
def selectBinData {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (hC : (roundedClass cuts hN P I D).Nonempty) : RoundedTypeData P :=
  { count := D.count
    binIndex := leastMaxBin (roundedClass cuts hN P I D)
      (fun x => ⌊-Real.log (massOn cuts x)⌋₊) hC }

@[simp] lemma selectBinData_count {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (hC : (roundedClass cuts hN P I D).Nonempty) :
    (selectBinData cuts hN P I D hC).count = D.count := rfl

@[simp] lemma roundedClass_selectBinData {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (hC : (roundedClass cuts hN P I D).Nonempty) :
    roundedClass cuts hN P I (selectBinData cuts hN P I D hC) =
      roundedClass cuts hN P I D := rfl

lemma selectedClass_selectBinData {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (hC : (roundedClass cuts hN P I D).Nonempty)
    (hp : ∀ x ∈ roundedClass cuts hN P I D, 0 < massOn cuts x) :
    selectedClass cuts hN P I (selectBinData cuts hN P I D hC) =
      indexFiber (roundedClass cuts hN P I D) (fun x => ⌊-Real.log (massOn cuts x)⌋₊)
        (leastMaxBin (roundedClass cuts hN P I D)
          (fun x => ⌊-Real.log (massOn cuts x)⌋₊) hC) := by
  exact massBin_eq_indexFiber cuts hN P I (selectBinData cuts hN P I D hC) hp _

/-- The binning part of the concrete specification follows from supported counts. -/
theorem typeDataSpec_of_counts {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hN2 : 2 ≤ N) (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    {xi alpha C : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hreg : P.IsRegular xi C)
    (htotal : ∀ i, ∑ l, D.count i l = cellPositionCount cuts hN P I i)
    (hsupport : ∀ i l, prob (P.rep i) l ≤ 2*xi → D.count i l = 0)
    (hround : ∀ i l, |(D.count i l : ℝ) - (cellPositionCount cuts hN P I i : ℝ) *
      retainedTilt P xi alpha i l| ≤ 1)
    (hdenom : ∀ i, 0 < ∑ l : Fin k,
      if 2*xi < prob (P.rep i) l then (prob (P.rep i) l)^alpha else 0)
    (hC : (roundedClass cuts hN P I D).Nonempty)
    (hcard : (roundedClass cuts hN P I D).card = ∏ i : Fin P.cellCount,
      (cellPositionCount cuts hN P I i).factorial / ∏ l : Fin k, (D.count i l).factorial) :
    TypeDataSpec cuts hN P I xi alpha (selectBinData cuts hN P I D hC) := by
  let E := selectBinData cuts hN P I D hC
  let s := roundedClass cuts hN P I D
  let f := fun x : WordOn k I => ⌊-Real.log (massOn cuts x)⌋₊
  have hlower := roundedClass_actual_lower cuts hN P I D hreg hsupport
  have hp : ∀ x ∈ s, 0 < massOn cuts x := fun x hx =>
    massOn_pos cuts x (fun j => hxi.trans_le (hlower x hx j))
  have heq : selectedClass cuts hN P I E = indexFiber s f (leastMaxBin s f hC) :=
    selectedClass_selectBinData cuts hN P I D hC hp
  have hsel : (selectedClass cuts hN P I E).Nonempty := by
    rw [heq]
    exact leastMaxBin_nonempty s f hC
  have hB : 0 ≤ Real.log (1 / xi) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hxi.le hxi1)
  have hbins : ((s.image f).card : ℝ) ≤ 2 + (I.card : ℝ)*Real.log (1/xi) :=
    floor_image_card_bound s _ _ (mul_nonneg (Nat.cast_nonneg _) hB)
      (fun x hx => (massOn_cost_bounds cuts hN x hxi (hlower x hx)).2)
  have hj : 0 ≤ typeJ N E := div_nonneg (Nat.cast_nonneg _) (logScale_pos hN2).le
  have hcardpos : 0 < (selectedClass cuts hN P I E).card := Finset.card_pos.mpr hsel
  have hh : 0 ≤ typeH cuts hN P I E := by
    apply div_nonneg _ (logScale_pos hN2).le
    apply Real.log_nonneg
    exact_mod_cast hcardpos
  refine ⟨htotal, hsupport, hround, hdenom, hC, hsel, hbins, hcard, ?_, ?_, hj, hh, ?_, ?_, hlower⟩
  · intro b
    rw [massBin_eq_indexFiber cuts hN P I E hp b, heq]
    exact leastMaxBin_maximal s f hC b
  · intro b hb
    rw [massBin_eq_indexFiber cuts hN P I E hp b, heq] at hb
    exact leastMaxBin_tie s f hC b hb
  · exact card_eq_rpow_log_div N _ hN2 hcardpos
  · exact selectedClass_exact_mass cuts hN hN2 P I E hp

end RiffleLowerV2.Types
