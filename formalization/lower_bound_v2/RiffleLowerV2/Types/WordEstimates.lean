import RiffleLowerV2.Types.MassBins

noncomputable section
open scoped BigOperators
open TimeProfile
namespace RiffleLowerV2.Types
attribute [local instance] Classical.propDecidable

lemma cellPositionCount_le_card {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (i : Fin P.cellCount) :
    cellPositionCount cuts hN P I i ≤ I.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma sum_cellPositionCount {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) :
    ∑ i, cellPositionCount cuts hN P I i = I.card := by
  simpa [cellPositionCount] using
    Finset.card_eq_sum_card_fiberwise (s := I) (t := Finset.univ)
      (f := fun j => P.classify (cuts.profile hN j)) (fun _ _ => Finset.mem_univ _)
      |>.symm

lemma cell_sum_identity {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (v : Fin P.cellCount → ℝ) :
    (∑ j ∈ I, v (P.classify (cuts.profile hN j))) =
      ∑ i, (cellPositionCount cuts hN P I i : ℝ) * v i := by
  simpa [cellPositionCount] using
    (Finset.sum_fiberwise' I (fun j => P.classify (cuts.profile hN j)) v).symm

lemma word_sum_identity {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (x : WordOn k I) (hx : x ∈ roundedClass cuts hN P I D)
    (v : Fin P.cellCount → Fin k → ℝ) :
    (∑ j : I, v (P.classify (cuts.profile hN j.val)) (x j)) =
      ∑ i, ∑ l, (D.count i l : ℝ) * v i l := by
  have hc := (Finset.mem_filter.mp hx).2
  calc
    (∑ j : I, v (P.classify (cuts.profile hN j.val)) (x j)) =
        ∑ a : Fin P.cellCount × Fin k,
          ∑ j ∈ Finset.univ.filter
            (fun j : I => (P.classify (cuts.profile hN j.val), x j) = a), v a.1 a.2 := by
      symm
      exact Finset.sum_fiberwise' Finset.univ
        (fun j : I => (P.classify (cuts.profile hN j.val), x j)) (fun a => v a.1 a.2)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      simp only [Prod.mk.injEq, Finset.sum_const, nsmul_eq_mul]
      rw [show (Finset.univ.filter (fun j : I =>
        P.classify (cuts.profile hN j.val) = i ∧ x j = l)).card = D.count i l from hc i l]

lemma digitCost_bounds_of_cutoff {p xi : ℝ} (hxi : 0 < xi) (hp : xi ≤ p)
    (hp1 : p ≤ 1) : 0 ≤ digitCost p ∧ digitCost p ≤ Real.log (1 / xi) := by
  simp only [digitCost, one_div, Real.log_inv]
  exact ⟨neg_nonneg.mpr (Real.log_nonpos (hxi.trans_le hp).le hp1),
    neg_le_neg (Real.log_le_log hxi hp)⟩

lemma raw_word_cost_error {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    {xi C : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hreg : P.IsRegular xi C)
    (q : Fin P.cellCount → Fin k → ℝ)
    (hD : ∀ i l, prob (P.rep i) l ≤ 2*xi → D.count i l = 0)
    (hq : ∀ i l, prob (P.rep i) l ≤ 2*xi → q i l = 0)
    (herr : ∀ i l, |(D.count i l : ℝ) - (cellPositionCount cuts hN P I i : ℝ)*q i l| ≤ 1)
    (x : WordOn k I) (hx : x ∈ roundedClass cuts hN P I D) :
    |-Real.log (massOn cuts x) -
      ∑ i, (cellPositionCount cuts hN P I i : ℝ) *
        (∑ l, q i l * digitCost (prob (P.rep i) l))| ≤
      C*xi*(I.card : ℝ) + (k : ℝ)*P.cellCount*Real.log (1/xi) := by
  let r := fun j : I => P.rep (P.classify (cuts.profile hN j.val))
  have hcount := (Finset.mem_filter.mp hx).2
  have hgood (j : I) : 2*xi < prob (r j) (x j) := by
    have hp : 0 < wordCellCount cuts hN P x
        (P.classify (cuts.profile hN j.val)) (x j) :=
      Finset.card_pos.mpr ⟨j, by simp⟩
    by_contra hh
    rw [hcount, hD _ _ (le_of_not_gt hh)] at hp
    exact (Nat.lt_irrefl 0) hp
  have hactual (j : I) := hreg.good_digit (P.classify (cuts.profile hN j.val))
    (cuts.profile hN j.val) (x j) rfl (hgood j)
  have hp (j : I) : 0 < (cuts.count j.val (x j) : ℝ)/N := hxi.trans (hactual j).1
  have hlog : -Real.log (massOn cuts x) =
      ∑ j : I, digitCost (prob (cuts.profile hN j.val) (x j)) := by
    rw [massOn, Real.log_prod (fun j _ => (hp j).ne'), ← Finset.sum_neg_distrib]
    simp only [Cuts.profile_prob, digitCost, one_div, Real.log_inv]
  have hreplace : |-Real.log (massOn cuts x) - ∑ j : I, digitCost (prob (r j) (x j))| ≤
      C*xi*(I.card : ℝ) := by
    rw [hlog, ← Finset.sum_sub_distrib]
    calc
      |∑ j : I, (digitCost (prob (cuts.profile hN j.val) (x j)) -
          digitCost (prob (r j) (x j)))| ≤
          ∑ j : I, |digitCost (prob (cuts.profile hN j.val) (x j)) -
            digitCost (prob (r j) (x j))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : I, C*xi := Finset.sum_le_sum fun j _ => (hactual j).2
      _ = _ := by simp [mul_comm]
  have hround : |(∑ i, ∑ l, (D.count i l : ℝ)*digitCost (prob (P.rep i) l)) -
      ∑ i, (cellPositionCount cuts hN P I i : ℝ) *
        (∑ l, q i l * digitCost (prob (P.rep i) l))| ≤
      (k : ℝ)*P.cellCount*Real.log (1/xi) := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ i, |∑ l, ((D.count i l : ℝ) -
          (cellPositionCount cuts hN P I i : ℝ)*q i l) * digitCost (prob (P.rep i) l)|) ≤
          ∑ _i : Fin P.cellCount, ∑ _l : Fin k, Real.log (1/xi) := by
        apply Finset.sum_le_sum
        intro i _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro l _
        by_cases hret : 2*xi < prob (P.rep i) l
        · have hb := digitCost_bounds_of_cutoff hxi (by linarith : xi ≤ prob (P.rep i) l)
            (prob_le_one (P.rep i) l)
          rw [abs_mul, abs_of_nonneg hb.1]
          exact (mul_le_mul_of_nonneg_right (herr i l) hb.1).trans (by simpa using hb.2)
        · rw [hD i l (le_of_not_gt hret), hq i l (le_of_not_gt hret)]
          simp only [Nat.cast_zero, mul_zero, sub_self, zero_mul, abs_zero]
          have hb := digitCost_bounds_of_cutoff hxi hxi1 (le_refl (1 : ℝ))
          simpa [digitCost] using hb.2
      _ = _ := by simp; ring
  have hgroup := word_sum_identity cuts hN P I D x hx (fun i l => digitCost (prob (P.rep i) l))
  have htri := abs_sub_le (-Real.log (massOn cuts x))
    (∑ j : I, digitCost (prob (r j) (x j)))
    (∑ i, (cellPositionCount cuts hN P I i : ℝ) *
      (∑ l, q i l * digitCost (prob (P.rep i) l)))
  rw [show (∑ j : I, digitCost (prob (r j) (x j))) =
    ∑ i, ∑ l, (D.count i l : ℝ) * digitCost (prob (P.rep i) l) from hgroup] at htri hreplace
  exact htri.trans (add_le_add hreplace hround)

lemma cell_sum_error {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (v : Fin P.cellCount → ℝ)
    (f : Fin K → ℝ) (e : ℝ)
    (he : ∀ j ∈ I, |v (P.classify (cuts.profile hN j)) - f j| ≤ e) :
    |(∑ i, (cellPositionCount cuts hN P I i : ℝ) * v i) - ∑ j ∈ I, f j| ≤
      (I.card : ℝ) * e := by
  rw [← cell_sum_identity, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum he).trans_eq (by simp))

lemma selectedJ_error_of_raw_cost {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hN2 : 2 ≤ N) (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (hsel : (selectedClass cuts hN P I D).Nonempty) (a e : ℝ)
    (he : ∀ x ∈ roundedClass cuts hN P I D, |-Real.log (massOn cuts x) - a| ≤ e) :
    |typeJ N D - a / logScale N| ≤ (e+1) / logScale N := by
  obtain ⟨x, hx⟩ := hsel
  obtain ⟨hx0, hlo, hhi⟩ := Finset.mem_filter.mp hx
  have hf : |(D.binIndex : ℝ) - (-Real.log (massOn cuts x))| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have ht := (abs_sub_le (D.binIndex : ℝ) (-Real.log (massOn cuts x)) a).trans
    (add_le_add hf (he x hx0))
  dsimp [typeJ]
  rw [← sub_div, abs_div, abs_of_pos (logScale_pos hN2)]
  exact div_le_div_of_nonneg_right (by linarith) (logScale_pos hN2).le

lemma selectedClass_log_loss {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (hsel : (selectedClass cuts hN P I D).Nonempty)
    (hpos : ∀ x ∈ roundedClass cuts hN P I D, 0 < massOn cuts x)
    (hmax : ∀ b, (massBin cuts hN P I D b).card ≤ (selectedClass cuts hN P I D).card)
    {B : ℝ} (hB : 0 < B)
    (hbins : (((roundedClass cuts hN P I D).image
      (fun x => ⌊-Real.log (massOn cuts x)⌋₊)).card : ℝ) ≤ B) :
    |Real.log (selectedClass cuts hN P I D).card -
      Real.log (roundedClass cuts hN P I D).card| ≤ Real.log B := by
  let s := roundedClass cuts hN P I D
  let t := selectedClass cuts hN P I D
  have ht : 0 < (t.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hsel
  have hsub : t ⊆ s := Finset.filter_subset _ _
  have hle : (t.card : ℝ) ≤ s.card := by exact_mod_cast Finset.card_le_card hsub
  have hs : 0 < (s.card : ℝ) := ht.trans_le hle
  have hprod : s.card ≤ t.card * (s.image (fun x => ⌊-Real.log (massOn cuts x)⌋₊)).card := by
    apply Finset.card_le_mul_card_image
    intro b _
    change (indexFiber (roundedClass cuts hN P I D)
      (fun x => ⌊-Real.log (massOn cuts x)⌋₊) b).card ≤ _
    rw [← massBin_eq_indexFiber cuts hN P I D hpos b]
    exact hmax b
  have hpr : (s.card : ℝ) ≤ t.card * B := by
    have hpr' : (s.card : ℝ) ≤ t.card *
        ((s.image (fun x => ⌊-Real.log (massOn cuts x)⌋₊)).card : ℝ) := by exact_mod_cast hprod
    exact hpr'.trans (mul_le_mul_of_nonneg_left hbins ht.le)
  have hl := Real.log_le_log hs hpr
  rw [Real.log_mul ht.ne' hB.ne'] at hl
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ht hle))]
  dsimp [s, t] at *
  linarith

lemma selectedH_error_of_raw_entropy {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hN2 : 2 ≤ N) (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (a e loss : ℝ)
    (he : |Real.log (roundedClass cuts hN P I D).card - a| ≤ e)
    (hloss : |Real.log (selectedClass cuts hN P I D).card -
      Real.log (roundedClass cuts hN P I D).card| ≤ loss) :
    |typeH cuts hN P I D - a / logScale N| ≤ (e+loss) / logScale N := by
  have ht := (abs_sub_le (Real.log (selectedClass cuts hN P I D).card)
    (Real.log (roundedClass cuts hN P I D).card) a).trans (add_le_add hloss he)
  dsimp [typeH]
  rw [← sub_div, abs_div, abs_of_pos (logScale_pos hN2)]
  exact div_le_div_of_nonneg_right (by linarith) (logScale_pos hN2).le

end RiffleLowerV2.Types
