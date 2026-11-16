import RiffleUpperV2.Reservoir.Cancellation

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem remainingPopulation_eq {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (A : Finset (Fin (pileSize cuts p))) :
    n-A.card = (n-pileSize cuts p) + (Finset.univ \ A).card := by
  have hr := pileOffset_add_size_le cuts p
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

def tailResidualTupleWeight {k n L r : ℕ} (cuts : Cuts k n (L+1))
    (A : Finset (Fin r)) (a w : Fin r → Word k (L+1)) : ℝ :=
  ∏ j : Fin L, (∏ d : Fin k,
    RiffleLowerV2.falling (cuts.count j.succ d - selectedDigitCount A a j.succ d)
      (selectedDigitCount (Finset.univ \ A) w j.succ d)) /
    RiffleLowerV2.falling (n-A.card) (Finset.univ \ A).card

def markedInitialWeight {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (A : Finset (Fin (pileSize cuts p))) : ℝ :=
  RiffleLowerV2.falling (pileSize cuts p-A.card) (Finset.univ \ A).card /
    RiffleLowerV2.falling (n-A.card) (Finset.univ \ A).card

theorem selectedDigitCount_first {k L r : ℕ} (A : Finset (Fin r))
    (a : Fin r → Word k (L+1)) (p : Fin k) (ha : ∀ q ∈ A, (a q).get 0 = p)
    (d : Fin k) : selectedDigitCount A a 0 d = if d=p then A.card else 0 := by
  by_cases hd : d=p
  · subst d
    simp only [selectedDigitCount, if_true]
    rw [Finset.filter_eq_self.mpr ha]
  · simp only [selectedDigitCount, hd, if_false]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro q hq h
    exact hd (h.symm.trans (ha q hq))

theorem residualTupleWeight_firstColumn {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (A : Finset (Fin (pileSize cuts p))) (a w : Fin (pileSize cuts p) → Word k (L+1))
    (ha : ∀ q ∈ A, (a q).get 0 = p) (hw : ∀ q, (w q).get 0 = p) :
    residualTupleWeight cuts A a w = markedInitialWeight cuts p A * tailResidualTupleWeight cuts A a w := by
  unfold residualTupleWeight
  rw [Fin.prod_univ_succ]
  apply congrArg (fun v : ℝ => v * tailResidualTupleWeight cuts A a w)
  unfold markedInitialWeight
  congr 1
  rw [Finset.prod_eq_single p]
  · rw [selectedDigitCount_first A a p ha p,
      selectedDigitCount_first (Finset.univ \ A) w p (fun q _ => hw q) p]
    simp only [if_true, pileSize]
  · intro d _ hd
    rw [selectedDigitCount_first (Finset.univ \ A) w p (fun q _ => hw q) d]
    simp [hd, RiffleLowerV2.falling]
  · simp

theorem markedInitialWeight_pos {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (A : Finset (Fin (pileSize cuts p))) : 0 < markedInitialWeight cuts p A := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hn := remainingPopulation_eq cuts p A
  apply div_pos <;> unfold RiffleLowerV2.falling <;>
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega)

/-- The first column is fully accounted for by conditioning on the labeled
pile. Its common factor cancels, leaving only later-column residual weights. -/
theorem exactTailResidualMarkedRowLaw {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω : Sample cuts)
    (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1))
    (ω₀ : Sample cuts) (ha : ∀ q ∈ A, tupleWords e ω₀ q = a q)
    (hap : ∀ q ∈ A, (a q).get 0 = p)
    (F : (Fin (pileSize cuts p) → Word k (L+1)) → ℝ) :
    conditionalExpect (fixedCountPMF cuts) (fun v => F (tupleWords e v))
      (fun v => (∀ q, (tupleWords e v q).get 0 = p) ∧
        historyFiber cuts p .forward (j.val+1) ω v ∧
        ∀ q ∈ A, tupleWords e v q = a q) =
    (∑ w : Fin (pileSize cuts p) → Word k (L+1),
      if tupleHistoryConstraint cuts p ω j w ∧ (∀ q ∈ A, w q = a q)
      then tailResidualTupleWeight cuts A a w * F w else 0) /
    (∑ w : Fin (pileSize cuts p) → Word k (L+1),
      if tupleHistoryConstraint cuts p ω j w ∧ (∀ q ∈ A, w q = a q)
      then tailResidualTupleWeight cuts A a w else 0) := by
  rw [exactResidualMarkedRowLaw cuts p e ω j A a ω₀ ha F]
  apply weightedRatio_cancel_factor _ _ _ _ (markedInitialWeight cuts p A)
    (ne_of_gt (markedInitialWeight_pos cuts p A))
  intro w hw
  exact residualTupleWeight_firstColumn cuts p A a w hap hw.1.1

end RiffleUpperV2.Reservoir
