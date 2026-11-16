import RiffleUpperV2.Reservoir.MarkedLaw

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

def selectedDigitCount {k L r : ℕ} (A : Finset (Fin r)) (w : Fin r → Word k L)
    (j : Fin L) (a : Fin k) : ℕ := (A.filter fun q => (w q).get j = a).card

def exposedWeight {k n L r : ℕ} (cuts : Cuts k n L) (A : Finset (Fin r))
    (a : Fin r → Word k L) : ℝ :=
  ∏ j : Fin L, (∏ d : Fin k, RiffleLowerV2.falling (cuts.count j d)
    (selectedDigitCount A a j d)) / RiffleLowerV2.falling n A.card

/-- Ordered marked-tuple weight on the exact residual population. The marked
indices are the complement of A; every exposed digit count is subtracted. -/
def residualTupleWeight {k n L r : ℕ} (cuts : Cuts k n L) (A : Finset (Fin r))
    (a w : Fin r → Word k L) : ℝ :=
  ∏ j : Fin L, (∏ d : Fin k,
    RiffleLowerV2.falling (cuts.count j d - selectedDigitCount A a j d)
      (selectedDigitCount (Finset.univ \ A) w j d)) /
    RiffleLowerV2.falling (n-A.card) (Finset.univ \ A).card

theorem selectedDigitCount_congr {k L r : ℕ} (A : Finset (Fin r))
    (a w : Fin r → Word k L) (h : ∀ q ∈ A, w q = a q) (j : Fin L) (d : Fin k) :
    selectedDigitCount A w j d = selectedDigitCount A a j d := by
  apply congrArg Finset.card
  exact Finset.filter_congr (fun q hq => by rw [h q hq])

theorem selectedDigitCount_split {k L r : ℕ} (A : Finset (Fin r))
    (w : Fin r → Word k L) (j : Fin L) (d : Fin k) :
    selectedDigitCount Finset.univ w j d = selectedDigitCount A w j d +
      selectedDigitCount (Finset.univ \ A) w j d := by
  have he : (A.filter fun q => (w q).get j = d) ∪
      ((Finset.univ \ A).filter fun q => (w q).get j = d) =
      Finset.univ.filter (fun q => (w q).get j = d) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  have hd : Disjoint (A.filter fun q => (w q).get j = d)
      ((Finset.univ \ A).filter fun q => (w q).get j = d) := by
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq').1).2 (Finset.mem_filter.mp hq).1
  exact (congrArg Finset.card he).symm.trans (Finset.card_union_of_disjoint hd)

theorem falling_add (n b m : ℕ) :
    RiffleLowerV2.falling n (b+m) =
      RiffleLowerV2.falling n b * RiffleLowerV2.falling (n-b) m := by
  have h := Nat.descFactorial_mul_descFactorial (n := n) (k := b) (m := b+m) (by omega)
  simp only [Nat.add_sub_cancel_left] at h
  unfold RiffleLowerV2.falling
  exact_mod_cast (h.symm.trans (Nat.mul_comm _ _))

/-- Exact cancellation identity, valid even when a marked allocation is
impossible. No approximation or positive-mass assumption is used here. -/
theorem tupleWeight_factor {k n L r : ℕ} (cuts : Cuts k n L) (A : Finset (Fin r))
    (a w : Fin r → Word k L) (h : ∀ q ∈ A, w q = a q) :
    tupleWeight cuts w = exposedWeight cuts A a * residualTupleWeight cuts A a w := by
  have hcard : r = A.card + (Finset.univ \ A).card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  unfold tupleWeight exposedWeight residualTupleWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hnum : (∏ d : Fin k, RiffleLowerV2.falling (cuts.count j d)
      (Finset.univ.filter fun q => (w q).get j = d).card) =
      (∏ d : Fin k, RiffleLowerV2.falling (cuts.count j d) (selectedDigitCount A a j d)) *
      (∏ d : Fin k, RiffleLowerV2.falling (cuts.count j d - selectedDigitCount A a j d)
        (selectedDigitCount (Finset.univ \ A) w j d)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro d _
    change RiffleLowerV2.falling (cuts.count j d) (selectedDigitCount Finset.univ w j d) = _
    rw [selectedDigitCount_split, selectedDigitCount_congr A a w h, falling_add]
  have hden := congrArg (RiffleLowerV2.falling n) hcard
  rw [falling_add] at hden
  rw [hnum, hden]
  exact mul_div_mul_comm _ _ _ _

theorem selectedDigitCount_le_cut {k n L r : ℕ} (cuts : Cuts k n L)
    (e : Fin r ↪ Fin n) (A : Finset (Fin r)) (a : Fin r → Word k L)
    (ω : Sample cuts) (h : ∀ q ∈ A, tupleWords e ω q = a q) (j : Fin L) (d : Fin k) :
    selectedDigitCount A a j d ≤ cuts.count j d := by
  have hs : (A.filter fun q => (a q).get j = d).map e ⊆
      Finset.univ.filter (fun q => (ω j).val q = d) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hq
    have ha := congrArg (fun w : Word k L => w.get j) (h x (Finset.mem_filter.mp hx).1)
    simp only [tupleWords, RiffleLowerV2.rowWord_get, sampleEntry] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.trans (Finset.mem_filter.mp hx).2⟩
  have hh := Finset.card_le_card hs
  rw [Finset.card_map, (ω j).property d] at hh
  exact hh

theorem exposedWeight_pos {k n L r : ℕ} (cuts : Cuts k n L)
    (e : Fin r ↪ Fin n) (A : Finset (Fin r)) (a : Fin r → Word k L)
    (ω : Sample cuts) (h : ∀ q ∈ A, tupleWords e ω q = a q) :
    0 < exposedWeight cuts A a := by
  apply Finset.prod_pos
  intro j _
  apply div_pos
  · apply Finset.prod_pos
    intro d _
    unfold RiffleLowerV2.falling
    exact_mod_cast Nat.descFactorial_pos.mpr (selectedDigitCount_le_cut cuts e A a ω h j d)
  · unfold RiffleLowerV2.falling
    apply Nat.cast_pos.mpr
    apply Nat.descFactorial_pos.mpr
    simpa only [Fintype.card_fin] using
      (Finset.card_le_univ A).trans (Fintype.card_le_of_embedding e)

theorem weightedRatio_cancel_factor {Ω : Type*} [Fintype Ω] (B : Ω → Prop) [DecidablePred B]
    (W V F : Ω → ℝ) (c : ℝ) (hc : c ≠ 0) (h : ∀ w, B w → W w = c * V w) :
    (∑ w, if B w then W w * F w else 0) / (∑ w, if B w then W w else 0) =
    (∑ w, if B w then V w * F w else 0) / (∑ w, if B w then V w else 0) := by
  have hnum : (∑ w, if B w then W w * F w else 0) =
      c * ∑ w, if B w then V w * F w else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : B w <;> simp [hw, h w, mul_assoc]
  have hden : (∑ w, if B w then W w else 0) =
      c * ∑ w, if B w then V w else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : B w <;> simp [hw, h w]
  rw [hnum, hden, mul_div_mul_left _ _ hc]

/-- Actual natural-history conditional law with the exposed-row factors
cancelled. With r=pileSize and m=r-|A|, the residual population n-|A| is c+m. -/
theorem exactResidualMarkedRowLaw {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω : Sample cuts)
    (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1))
    (ω₀ : Sample cuts) (ha : ∀ q ∈ A, tupleWords e ω₀ q = a q)
    (F : (Fin (pileSize cuts p) → Word k (L+1)) → ℝ) :
    conditionalExpect (fixedCountPMF cuts) (fun v => F (tupleWords e v))
      (fun v => (∀ q, (tupleWords e v q).get 0 = p) ∧
        historyFiber cuts p .forward (j.val+1) ω v ∧
        ∀ q ∈ A, tupleWords e v q = a q) =
    (∑ w : Fin (pileSize cuts p) → Word k (L+1),
      if tupleHistoryConstraint cuts p ω j w ∧ (∀ q ∈ A, w q = a q)
      then residualTupleWeight cuts A a w * F w else 0) /
    (∑ w : Fin (pileSize cuts p) → Word k (L+1),
      if tupleHistoryConstraint cuts p ω j w ∧ (∀ q ∈ A, w q = a q)
      then residualTupleWeight cuts A a w else 0) := by
  rw [exactMarkedRowLaw]
  apply weightedRatio_cancel_factor _ _ _ _ (exposedWeight cuts A a)
    (ne_of_gt (exposedWeight_pos cuts e A a ω₀ ha))
  intro w hw
  exact tupleWeight_factor cuts A a w hw.2

end RiffleUpperV2.Reservoir
