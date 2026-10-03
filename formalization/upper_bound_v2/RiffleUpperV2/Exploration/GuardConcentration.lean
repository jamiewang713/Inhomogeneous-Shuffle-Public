import RiffleUpperV2.Exploration.CylinderCounts
import RiffleUpperV2.Exploration.Guards

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open Hypergeometric Anchor RiffleUpperV2.Localization TimeProfile RiffleLowerV2.Thinning

def tailBinPrefix {k L : ℕ} (D : ℕ) (p : Fin k) (v : Word k (min D L)) : Prefix k (L+1) :=
  ⟨⟨min D L+1, by omega⟩, List.Vector.cons p v⟩

theorem tailBinPrefix_word {k L : ℕ} (D : ℕ) (p : Fin k)
    (v : Word k (min D L)) (w : Word k (L+1)) :
    w.toList.take (min D L+1) = (List.Vector.cons p v).toList ↔
      w.get 0 = p ∧ tailPrefix D w = v := by
  rw [vector_take_eq_iff (by omega)]
  simp only [Fin.forall_fin_succ, List.Vector.get_cons_zero, List.Vector.get_cons_succ]
  apply and_congr_right
  intro _
  constructor
  · intro h
    apply List.Vector.ext
    intro r
    simpa only [tailPrefix, List.Vector.get_ofFn, Fin.castLE, Fin.succ] using h r
  · intro h r
    have hh := congrArg (fun z => List.Vector.get z r) h
    simpa only [tailPrefix, List.Vector.get_ofFn, Fin.castLE, Fin.succ] using hh

def tailBinCount {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (p : Fin k)
    (v : Word k (min D L)) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun r : Fin n => (rowWord ω r).get 0 = p ∧ tailPrefix D (rowWord ω r) = v).card

theorem tailBinCount_prefix {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (p : Fin k)
    (v : Word k (min D L)) (ω : Sample cuts) :
    tailBinCount cuts D p v ω = prefixCount (tailBinPrefix D p v) ω := by
  unfold tailBinCount
  change _ = (Finset.univ.filter fun r : Fin n =>
    (rowWord ω r).toList.take (min D L+1) = (List.Vector.cons p v).toList).card
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, tailBinPrefix_word]

theorem tailBinCount_le_pile {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (p : Fin k)
    (v : Word k (min D L)) (ω : Sample cuts) : tailBinCount cuts D p v ω ≤ pileSize cuts p := by
  calc
    _ ≤ (Finset.univ.filter fun r : Fin n => (rowWord ω r).get 0 = p).card := by
      apply Finset.card_le_card
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.1⟩
    _ = _ := by simpa only [RiffleLowerV2.rowWord_get, sampleEntry, pileSize] using (ω 0).property p

theorem tailBinMean_le_pile {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (D : ℕ) (p : Fin k) (v : Word k (min D L)) : prefixMean cuts (tailBinPrefix D p v) ≤ pileSize cuts p := by
  rw [← prefixCylinder_mean cuts hn, cylinderMean_eq_expect]
  simp_rw [prefixCylinder_count, ← tailBinCount_prefix cuts D p v]
  apply (expect_mono (fixedCountPMF cuts) (g := fun _ => (pileSize cuts p : ℝ)) (fun ω => by exact_mod_cast tailBinCount_le_pile cuts D p v ω)).trans_eq
  exact RiffleLowerV2.Model.expect_const _ _

/-- The guard selector is deterministic, even when no reserve triple exists. -/
def guardBins {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ) (through : Bool) :
    Finset (Word k (min D L)) :=
  Finset.univ.filter fun v => ∃ z, chosenReserves cuts D g = some z ∧
    if through then v ≤ z.2.1 else v < z.2.1

theorem guardCount_sum {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (p : Fin k) (through : Bool) (ω : Sample cuts) :
    guardCount cuts D g p through ω =
      ∑ v ∈ guardBins cuts D g through, tailBinCount cuts D p v ω := by
  have hh := Finset.sum_card_fiberwise_eq_card_filter
    (s := Finset.univ.filter (fun r : Fin n => (rowWord ω r).get 0 = p))
    (t := guardBins cuts D g through) (g := fun r => tailPrefix D (rowWord ω r))
  simp only [Finset.filter_filter] at hh
  unfold tailBinCount
  rw [hh]
  unfold guardCount
  congr 1
  ext r
  cases through <;> simp [guardCount, guardBins, beforeMiddle, throughMiddle]

theorem guardMean_sum {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (D : ℕ) (g : ℝ) (p : Fin k) (through : Bool) :
    guardMean cuts D g p through =
      ∑ v ∈ guardBins cuts D g through, prefixMean cuts (tailBinPrefix D p v) := by
  have hb (v : Word k (min D L)) :
      RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => (tailBinCount cuts D p v ω : ℝ)) =
        prefixMean cuts (tailBinPrefix D p v) := by
    rw [← prefixCylinder_mean cuts hn, cylinderMean_eq_expect]
    congr 1
    funext ω
    rw [prefixCylinder_count, tailBinCount_prefix]
  unfold guardMean
  simp_rw [guardCount_sum, Nat.cast_sum]
  change RiffleLowerV2.expect (fixedCountPMF cuts)
    (fun ω => ∑ v ∈ guardBins cuts D g through, (tailBinCount cuts D p v ω : ℝ)) = _
  have he : RiffleLowerV2.expect (fixedCountPMF cuts)
      (fun ω => ∑ v ∈ guardBins cuts D g through, (tailBinCount cuts D p v ω : ℝ)) =
      ∑ v ∈ guardBins cuts D g through, RiffleLowerV2.expect (fixedCountPMF cuts)
        (fun ω => (tailBinCount cuts D p v ω : ℝ)) := by
    unfold RiffleLowerV2.expect
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he]
  exact Finset.sum_congr rfl (fun v _ => hb v)

theorem guardBins_card_le {k n L : ℕ} (cuts : Cuts k n (L+1)) (hk : 1 ≤ k)
    (D : ℕ) (g : ℝ) (through : Bool) : (guardBins cuts D g through).card ≤ k^D := by
  apply (Finset.card_le_univ _).trans
  simp only [RiffleLowerV2.Word, RiffleShuffle.Word, card_vector, Fintype.card_fin]
  exact Nat.pow_le_pow_right hk (min_le_left D L)

/-- Both guards follow by summing the actual disjoint tail-prefix cylinders. -/
theorem allCylinder_guard_deviation {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (hk : 1 ≤ k) (D : ℕ) (g : ℝ) {ξ : ℝ} {ω : Sample cuts} (h : allCylinderEvent cuts ξ ω)
    (p : Fin k) (hp : (n : ℝ)^ξ ≤ pileSize cuts p) (through : Bool) :
    |(guardCount cuts D g p through ω : ℝ)-guardMean cuts D g p through| ≤
      (k : ℝ)^D * (pileSize cuts p : ℝ)^((2:ℝ)/3)/2 := by
  rw [guardCount_sum, guardMean_sum cuts hn]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _v ∈ guardBins cuts D g through, (pileSize cuts p : ℝ)^((2:ℝ)/3)/2 := by
      apply Finset.sum_le_sum
      intro v _
      have hh := allCylinderEvent_bound cuts h (prefixDigits (tailBinPrefix D p v)) hp
        (by rw [prefixCylinder_mean cuts hn]; exact tailBinMean_le_pile cuts hn D p v)
      rw [prefixCylinder_count, prefixCylinder_mean cuts hn, ← tailBinCount_prefix] at hh
      exact hh
    _ = ((guardBins cuts D g through).card : ℝ) * ((pileSize cuts p : ℝ)^((2:ℝ)/3)/2) := by simp
    _ ≤ (k : ℝ)^D * ((pileSize cuts p : ℝ)^((2:ℝ)/3)/2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast guardBins_card_le cuts hk D g through
    _ = _ := by ring

/-- Explicit scalar threshold for the guards, including the denominator-four replacement. -/
theorem guard_scale_bound {m d q : ℝ} (hm : 0 < m) (hd : 0 < d)
    (h : 2*q/d ≤ m^((1:ℝ)/3)) : q*m^((2:ℝ)/3)/2 ≤ d*m/4 := by
  have hh : 2*q ≤ m^((1:ℝ)/3)*d := (div_le_iff₀ hd).mp h
  have ht := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hm.le ((2:ℝ)/3))
  have he : m^((1:ℝ)/3)*m^((2:ℝ)/3) = m := by
    rw [← Real.rpow_add hm]
    norm_num
  nlinarith [he]

/-- Deterministic implication from the stronger event to the exact frozen H. -/
theorem allCylinder_implies_concentration {k n L : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) (hk : 1 ≤ k) (D : ℕ) {g ξ : ℝ} (hg : 0 < g) (hξ : ξ ≤ 1)
    (hscale : 2*(k : ℝ)^D/reserveMass k D g ≤ (n : ℝ)^(ξ/3))
    {ω : Sample cuts} (h : allCylinderEvent cuts ξ ω) : concentrationEvent cuts D g ξ ω := by
  refine ⟨fun p j a hj => allCylinder_outside cuts hn hξ h p j a hj,
    fun x hx => allCylinder_prefix_and_later cuts hn h x hx, ?_⟩
  intro p hp through
  apply (allCylinder_guard_deviation cuts hn hk D g h p hp through).trans
  have hm : (0:ℝ) < pileSize cuts p := (Real.rpow_pos_of_pos (by exact_mod_cast hn) ξ).trans_le hp
  have hd : 0 < reserveMass k D g := reserveMass_pos (by omega) hg
  apply guard_scale_bound hm hd
  apply hscale.trans
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) ξ) hp
    (by norm_num : (0:ℝ)≤1/3)
  rw [← Real.rpow_mul (Nat.cast_nonneg n)] at hh
  convert hh using 1 <;> congr 1 <;> ring

end RiffleUpperV2.Exploration

