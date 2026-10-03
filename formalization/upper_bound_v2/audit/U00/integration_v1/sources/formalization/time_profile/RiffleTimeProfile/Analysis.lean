import RiffleTimeProfile.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Lattice

open scoped BigOperators
open Set MeasureTheory

namespace TimeProfile

/- F05: one-column costs on the closed simplex, including zero coordinates. -/
theorem powerSum_pos {k : ℕ} (p : Simplex k) {theta : ℝ} (_htheta : 1 ≤ theta) :
    0 < powerSum p theta := by
  obtain ⟨l, hl⟩ := exists_prob_pos p
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hl theta)
    (Finset.single_le_sum (fun i _ => Real.rpow_nonneg (prob_nonneg p i) theta)
      (Finset.mem_univ l))

theorem powerSum_le_one {k : ℕ} (_hk : 2 ≤ k) (p : Simplex k) {theta : ℝ}
    (htheta : theta ∈ Icc (2 : ℝ) 4) :
    powerSum p theta ≤ 1 := by
  calc
    powerSum p theta ≤ ∑ l, prob p l := by
      exact Finset.sum_le_sum fun l _ =>
        Real.rpow_le_self_of_le_one (prob_nonneg p l) (prob_le_one p l)
          (by linarith [htheta.1])
    _ = 1 := sum_prob p

theorem maxCost_bounds {k : ℕ} (hk : 2 ≤ k) (p : Simplex k) :
    0 ≤ maxCost p ∧ maxCost p ≤ Real.log (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 < pileMax p := pileMax_pos p
  have hcard := inv_card_le_pileMax (by omega : 0 < k) p
  have hmul : 1 ≤ pileMax p * (k : ℝ) := (div_le_iff₀ hkpos).mp hcard
  have hinv : 1 / pileMax p ≤ (k : ℝ) := (div_le_iff₀ hp).mpr (by nlinarith)
  constructor
  · change 0 ≤ Real.log (1 / pileMax p)
    apply Real.log_nonneg
    exact (one_le_div hp).mpr (pileMax_le_one p)
  · exact Real.log_le_log (one_div_pos.mpr hp) hinv

theorem psi_bounds {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {theta : ℝ} (htheta : theta ∈ Icc (2 : ℝ) 4) :
    0 ≤ psi p theta ∧ psi p theta ≤ 4 * Real.log (k : ℝ) := by
  have ht : 1 ≤ theta := by linarith [htheta.1]
  have hz := powerSum_pos p ht
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hsum : (∑ _ : Fin k, (1 : ℝ) / k) ≤ ∑ l, prob p l := by
    simp [sum_prob, hkne]
  obtain ⟨l, _, hl⟩ := Finset.exists_le_of_sum_le hne hsum
  have hlpos : 0 < prob p l := lt_of_lt_of_le (one_div_pos.mpr hkpos) hl
  have hterm : prob p l ^ theta ≤ powerSum p theta :=
    Finset.single_le_sum (fun i _ => Real.rpow_nonneg (prob_nonneg p i) theta)
      (Finset.mem_univ l)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hlpos theta) hterm
  rw [Real.log_rpow hlpos theta] at hlog
  have hinv : 1 / prob p l ≤ (k : ℝ) := (div_le_iff₀ hlpos).mpr
    (by have := (div_le_iff₀ hkpos).mp hl; nlinarith)
  have hcost : -Real.log (prob p l) ≤ Real.log (k : ℝ) := by
    simpa only [one_div, Real.log_inv] using
      Real.log_le_log (one_div_pos.mpr hlpos) hinv
  have hklog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hm := mul_le_mul_of_nonneg_left hcost (by linarith [htheta.1] : 0 ≤ theta)
  have htlog := mul_le_mul_of_nonneg_right htheta.2 hklog
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos hz.le (powerSum_le_one hk p htheta))
  · dsimp [psi]
    nlinarith

/- E01: the finite Gibbs inequality, with its zero-total branch included. -/
theorem finite_gibbs {k : ℕ} (p : Simplex k) (c : Fin k → ℝ)
    (hc : ∀ l, 0 ≤ c l) {theta : ℝ} (htheta : 1 ≤ theta)
    (hsupport : ∀ l, 0 < c l → 0 < prob p l) :
    (∑ l, if 0 < c l then c l * Real.log ((∑ i, c i) / c l) else 0) ≤
      theta * (∑ l, c l * digitCost (prob p l)) +
        (∑ l, c l) * Real.log (powerSum p theta) := by
  classical
  let C : ℝ := ∑ l, c l
  let Z : ℝ := powerSum p theta
  have hC : 0 ≤ C := Finset.sum_nonneg (fun l _ => hc l)
  have hZ : 0 < Z := powerSum_pos p htheta
  by_cases hCzero : C = 0
  · have hc_zero : ∀ l, c l = 0 := by
      intro l
      have hle : c l ≤ C := Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ l)
      exact le_antisymm (by simpa [hCzero] using hle) (hc l)
    simp [hc_zero]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hterm : ∀ l,
        (if 0 < c l then c l * Real.log (C / c l) else 0) ≤
          theta * (c l * digitCost (prob p l)) + c l * Real.log Z +
            C * (prob p l ^ theta) / Z - c l := by
      intro l
      by_cases hl : 0 < c l
      · have hp := hsupport l hl
        have hpPow := Real.rpow_pos_of_pos hp theta
        have hratio : 0 < C * (prob p l ^ theta) / (c l * Z) :=
          div_pos (mul_pos hCpos hpPow) (mul_pos hl hZ)
        have hlog : Real.log (C * (prob p l ^ theta) / (c l * Z)) =
            Real.log (C / c l) + theta * Real.log (prob p l) - Real.log Z := by
          rw [Real.log_div (ne_of_gt (mul_pos hCpos hpPow)) (ne_of_gt (mul_pos hl hZ)),
            Real.log_mul (ne_of_gt hCpos) (ne_of_gt hpPow),
            Real.log_mul (ne_of_gt hl) (ne_of_gt hZ),
            Real.log_div (ne_of_gt hCpos) (ne_of_gt hl), Real.log_rpow hp theta]
          ring
        have hineq := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) (hc l)
        rw [hlog] at hineq
        have hcancel : c l * (C * (prob p l ^ theta) / (c l * Z) - 1) =
            C * (prob p l ^ theta) / Z - c l := by
          field_simp
        rw [hcancel] at hineq
        simp only [if_pos hl, digitCost, one_div, Real.log_inv]
        nlinarith
      · have hzero : c l = 0 := le_antisymm (le_of_not_gt hl) (hc l)
        simp only [hzero, lt_self_iff_false, if_false, zero_mul, mul_zero,
          zero_add, sub_zero]
        exact div_nonneg (mul_nonneg hC (Real.rpow_nonneg (prob_nonneg p l) theta)) hZ.le
    have hsum := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hterm l)
    have hsumPow : (∑ l, prob p l ^ theta) = Z := rfl
    have hcancelSum : (∑ l, C * (prob p l ^ theta) / Z) = C := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hsumPow, mul_div_cancel_right₀ _ (ne_of_gt hZ)]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul] at hsum
    rw [show (∑ l, C * (prob p l ^ theta) / Z) = C from hcancelSum] at hsum
    change (∑ l, if 0 < c l then c l * Real.log (C / c l) else 0) ≤
      theta * (∑ l, c l * digitCost (prob p l)) + C * Real.log Z
    dsimp [C] at hsum ⊢
    linarith

/- F09: a finite Borel partition with a uniform, fixed regularity constant. -/
theorem exists_regular_partition {k : ℕ} (_hk : 2 ≤ k) {chi : ℝ}
    (hchi : 0 < chi) (_hchiK : chi < 1 / (k : ℝ)) :
    ∃ P : BorelPartition k, P.IsRegular chi 1 := by
  classical
  have hcoord (l : Fin k) : Continuous (fun p : Simplex k => prob p l) :=
    (continuous_apply l).comp continuous_subtype_val
  have hmax : Continuous (fun p : Simplex k => pileMax p) := by
    unfold pileMax
    exact NNReal.continuous_coe.comp (Continuous.finset_sup_apply
      (s := Finset.univ) (fun l _ => (hcoord l).subtype_mk (fun p => prob_nonneg p l)))
  have ha : Continuous (fun p : Simplex k => maxCost p) := by
    convert (hmax.log (fun p => (pileMax_pos p).ne')).neg using 1
    ext p
    simp [maxCost, digitCost]
  let Theta := ↥(Icc (2 : ℝ) 4)
  have hz : Continuous (fun z : Simplex k × Theta => powerSum z.1 z.2) := by
    apply continuous_finsetSum
    intro l _
    exact ((hcoord l).comp continuous_fst).rpow
      (continuous_subtype_val.comp continuous_snd)
      (fun z => Or.inr (by have := z.2.property.1; linarith))
  have hpsi : Continuous (fun z : Simplex k × Theta => psi z.1 z.2) := by
    exact (hz.log (fun z => (powerSum_pos z.1 (by have := z.2.property.1; linarith)).ne')).neg
  have htrunc : Continuous (fun p : Simplex k => fun l : Fin k =>
      digitCost (max (prob p l) chi)) := by
    apply continuous_pi
    intro l
    have hm : Continuous (fun p : Simplex k => max (prob p l) chi) :=
      (hcoord l).max continuous_const
    have hmpos (p : Simplex k) : 0 < max (prob p l) chi :=
      hchi.trans_le (le_max_right _ _)
    convert (hm.log (fun p => (hmpos p).ne')).neg using 1
    ext p
    simp [digitCost]
  obtain ⟨da, hda, hauc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous ha) chi hchi
  obtain ⟨dp, hdp, hpuc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hpsi) chi hchi
  obtain ⟨dt, hdt, htuc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous htrunc) chi hchi
  let d : ℝ := min da (min dp (min dt chi)) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hda' : d < da := by
    have := min_le_left da (min dp (min dt chi))
    dsimp [d]
    linarith
  have hdp' : d < dp := by
    have h1 := min_le_right da (min dp (min dt chi))
    have h2 := min_le_left dp (min dt chi)
    dsimp [d]
    linarith
  have hdt' : d < dt := by
    have h1 := min_le_right da (min dp (min dt chi))
    have h2 := min_le_right dp (min dt chi)
    have h3 := min_le_left dt chi
    dsimp [d]
    linarith
  have hdchi : d < chi := by
    have h1 := min_le_right da (min dp (min dt chi))
    have h2 := min_le_right dp (min dt chi)
    have h3 := min_le_right dt chi
    dsimp [d]
    linarith
  let m : ℕ := ⌈1 / d⌉₊ + 1
  have hbound (p : Simplex k) (l : Fin k) : ⌊prob p l / d⌋₊ < m := by
    exact lt_of_le_of_lt (Nat.floor_le_floor
      (div_le_div_of_nonneg_right (prob_le_one p l) hd.le))
      (Nat.lt_succ_of_le (Nat.floor_le_ceil (1 / d)))
  let raw : Simplex k → (Fin k → Fin m) := fun p l =>
    ⟨⌊prob p l / d⌋₊, hbound p l⟩
  have hraw : Measurable raw := by
    apply measurable_pi_lambda
    intro l
    apply measurable_to_countable'
    intro n
    have hnatfloor : Measurable (Nat.floor : ℝ → ℕ) := by
      apply measurable_to_countable
      intro z
      rcases eq_or_ne ⌊z⌋₊ 0 with h | h <;>
        simp [h, Nat.preimage_floor_of_ne_zero, -Nat.floor_eq_zero]
    have hfloor : Measurable (fun p : Simplex k => ⌊prob p l / d⌋₊) :=
      hnatfloor.comp ((hcoord l).div_const d).measurable
    convert hfloor (measurableSet_singleton n.val) using 1
    ext p
    simp only [mem_preimage, mem_singleton_iff, raw, Fin.ext_iff]
  have hclose {p q : Simplex k} (heq : raw p = raw q) : dist p q < d := by
    apply (dist_pi_lt_iff hd).mpr
    intro l
    have hfloor : ⌊prob p l / d⌋₊ = ⌊prob q l / d⌋₊ :=
      congrArg (fun f : Fin k → Fin m => (f l).val) heq
    have hp0 : 0 ≤ prob p l / d := div_nonneg (prob_nonneg p l) hd.le
    have hq0 : 0 ≤ prob q l / d := div_nonneg (prob_nonneg q l) hd.le
    have hp1 := Nat.floor_le hp0
    have hp2 := Nat.lt_floor_add_one (prob p l / d)
    have hq1 := Nat.floor_le hq0
    have hq2 := Nat.lt_floor_add_one (prob q l / d)
    rw [hfloor] at hp1 hp2
    have hpq : prob p l / d - prob q l / d < 1 := by linarith
    have hqp : prob q l / d - prob p l / d < 1 := by linarith
    rw [← sub_div] at hpq hqp
    have hpq' := (div_lt_iff₀ hd).mp hpq
    have hqp' := (div_lt_iff₀ hd).mp hqp
    change |prob p l - prob q l| < d
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  let I := Set.range raw
  let : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let reps : I → Simplex k := fun i => Classical.choose i.property
  have hreps (i : I) : raw (reps i) = i.val := Classical.choose_spec i.property
  let cls : Simplex k → Fin (Fintype.card I) := fun p => e ⟨raw p, ⟨p, rfl⟩⟩
  have hcls : Measurable cls := by
    exact (measurable_of_finite e).comp (hraw.subtype_mk (h := fun p => ⟨p, rfl⟩))
  let P : BorelPartition k :=
    { cellCount := Fintype.card I
      classify := cls
      measurable_classify := hcls
      rep := fun i => reps (e.symm i)
      classify_rep := by
        intro i
        change e ⟨raw (reps (e.symm i)), _⟩ = i
        have hsub : (⟨raw (reps (e.symm i)), ⟨reps (e.symm i), rfl⟩⟩ : I) = e.symm i :=
          Subtype.ext (hreps (e.symm i))
        rw [hsub, e.apply_symm_apply] }
  have hcell {p q : Simplex k} (heq : P.classify p = P.classify q) : dist p q < d := by
    apply hclose
    exact congrArg Subtype.val (e.injective heq)
  have hcoordclose {p q : Simplex k} (heq : P.classify p = P.classify q) (l : Fin k) :
      |prob p l - prob q l| < chi := by
    have hc := (dist_pi_lt_iff hd).mp (hcell heq) l
    change |prob p l - prob q l| < d at hc
    exact hc.trans hdchi
  refine ⟨P, ?_⟩
  constructor
  · intro i p q hp hq theta htheta
    have hdist := hcell (hp.trans hq.symm)
    have hpair : dist (p, (⟨theta, htheta⟩ : Theta)) (q, (⟨theta, htheta⟩ : Theta)) < dp := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hdist.trans hdp'
    have h := hpuc hpair
    simpa only [Real.dist_eq, one_mul] using h.le
  · intro i p q hp hq
    have h := hauc ((hcell (hp.trans hq.symm)).trans hda')
    simpa only [Real.dist_eq, one_mul] using h.le
  · intro i p l hp hg
    have heq : P.classify p = P.classify (P.rep i) := hp.trans (P.classify_rep i).symm
    have hco := hcoordclose heq l
    have hactual : chi < prob p l := by
      have := (abs_lt.mp hco).1
      linarith
    have hrep : chi < prob (P.rep i) l := by linarith
    refine ⟨hactual, ?_⟩
    have ht := htuc ((hcell heq).trans hdt')
    have hi := (dist_pi_lt_iff hchi).mp ht l
    simpa only [Real.dist_eq, max_eq_left hactual.le, max_eq_left hrep.le, one_mul] using hi.le
  · intro i p l hp he
    have heq : P.classify p = P.classify (P.rep i) := hp.trans (P.classify_rep i).symm
    have hco := (abs_lt.mp (hcoordclose heq l)).2
    linarith

end TimeProfile
