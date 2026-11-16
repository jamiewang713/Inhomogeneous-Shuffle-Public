import FirstMomentModel.StableNumericalBridge
import FirstMomentModel.ProfileFibreEntropy
import RiffleTimeProfile.Digits

namespace InhomogeneousShuffle.FirstMoment.Model

noncomputable section
open scoped BigOperators

def sourceCell (D : Riffle.Model) (P : TimeProfile.BorelPartition D.k)
    {R : ℕ} (timeClass : Fin D.K → Fin R) : Fin D.K → Fin (R * P.cellCount) :=
  fun j => finProdFinEquiv (timeClass j, P.classify (asProfile D j))

def sourceGood (D : Riffle.Model) (P : TimeProfile.BorelPartition D.k)
    (chi : ℝ) : Fin D.K → ℕ → Prop :=
  fun j a => ∃ ha : a < D.k, P.IsGoodDigit chi (asProfile D j) ⟨a, ha⟩

theorem sourceGood_fin_iff (D : Riffle.Model) (P : TimeProfile.BorelPartition D.k)
    (chi : ℝ) (j : Fin D.K) (l : Fin D.k) :
    sourceGood D P chi j l.val ↔ P.IsGoodDigit chi (asProfile D j) l := by
  constructor
  · rintro ⟨h, hh⟩
    exact hh
  · intro h
    exact ⟨l.isLt, h⟩

variable {D : Riffle.Model} {R : ℕ}

theorem exceptionalPositions_source_eq (A : Riffle.Setup D)
    (P : TimeProfile.BorelPartition D.k) (chi : ℝ)
    (y z x : Riffle.Word) (hx : Riffle.Legal D x) :
    exceptionalPositions A (sourceGood D P chi) y z x =
      TimeProfile.exceptionalPositions (asProfile D) (legalVector x hx) P chi
        (Riffle.join y z).length x.length := by
  classical
  ext j
  simp only [exceptionalPositions, TimeProfile.exceptionalPositions,
    TimeProfile.positions, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hj : j.val < x.length
  · have hg : sourceGood D P chi j (Riffle.digit x j.val) ↔
        P.IsGoodDigit chi (asProfile D j) (legalVector x hx j) := by
      rw [← legalVector_digit x hx j hj]
      exact sourceGood_fin_iff D P chi j (legalVector x hx j)
    tauto
  · tauto

theorem digitCount_source_eq (A : Riffle.Setup D)
    (P : TimeProfile.BorelPartition D.k) (timeClass : Fin D.K → Fin R)
    (chi : ℝ) (y z x : Riffle.Word) (hx : Riffle.Legal D x)
    (a : Fin R × Fin P.cellCount × Fin D.k) :
    TimeProfile.digitCount D.N (asProfile D) (legalVector x hx) P timeClass chi
        (Riffle.join y z).length x.length a =
      (goodDigitCount A (sourceCell D P timeClass) (sourceGood D P chi)
        y z x (finProdFinEquiv (a.1, a.2.1)) a.2.2 : ℝ) /
        Real.log (D.N : ℝ) := by
  classical
  have hsets :
      (TimeProfile.goodPositions (asProfile D) (legalVector x hx) P chi
        (Riffle.join y z).length x.length).filter
          (fun j => TimeProfile.digitKey (asProfile D) (legalVector x hx) P timeClass j = a) =
      Finset.univ.filter (fun j : Fin D.K =>
        (Riffle.join y z).length ≤ j.val ∧ j.val < x.length ∧
        sourceCell D P timeClass j = finProdFinEquiv (a.1, a.2.1) ∧
        Riffle.digit x j.val = a.2.2.val ∧ sourceGood D P chi j (Riffle.digit x j.val)) := by
    ext j
    simp only [TimeProfile.goodPositions, TimeProfile.positions,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j.val < x.length
    · have hg : sourceGood D P chi j (Riffle.digit x j.val) ↔
          P.IsGoodDigit chi (asProfile D j) (legalVector x hx j) := by
        rw [← legalVector_digit x hx j hj]
        exact sourceGood_fin_iff D P chi j (legalVector x hx j)
      have hcell : sourceCell D P timeClass j = finProdFinEquiv (a.1, a.2.1) ↔
          timeClass j = a.1 ∧ P.classify (asProfile D j) = a.2.1 := by
        change finProdFinEquiv _ = finProdFinEquiv _ ↔ _
        rw [finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
      have hd : legalVector x hx j = a.2.2 ↔ Riffle.digit x j.val = a.2.2.val := by
        rw [Fin.ext_iff, legalVector_digit x hx j hj]
      have hkey : TimeProfile.digitKey (asProfile D) (legalVector x hx) P timeClass j = a ↔
          timeClass j = a.1 ∧ P.classify (asProfile D j) = a.2.1 ∧
            Riffle.digit x j.val = a.2.2.val := by
        change (timeClass j, P.classify (asProfile D j), legalVector x hx j) = a ↔ _
        rcases a with ⟨a₀, a₁, a₂⟩
        simp only [Prod.mk.injEq, hd]
      tauto
    · tauto
  simp only [TimeProfile.digitCount, TimeProfile.logScale, goodDigitCount, hsets]

theorem profileR_source_eq (A : Riffle.Setup D)
    (P : TimeProfile.BorelPartition D.k) (chi : ℝ)
    (y z x : Riffle.Word) (hx : Riffle.Legal D x) :
    TimeProfile.profileR D.N (asProfile D) (legalVector x hx) P chi
        (Riffle.join y z).length x.length =
      ((exceptionalPositions A (sourceGood D P chi) y z x).card : ℝ) /
        Real.log (D.N : ℝ) := by
  rw [TimeProfile.profileR, ← exceptionalPositions_source_eq A P chi y z x hx]
  rfl

theorem profileH_source_eq (A : Riffle.Setup D)
    (P : TimeProfile.BorelPartition D.k) (timeClass : Fin D.K → Fin R)
    (chi : ℝ) (y z x : Riffle.Word) (hx : Riffle.Legal D x) :
    TimeProfile.profileH D.N (asProfile D) (legalVector x hx) P timeClass chi
        (Riffle.join y z).length x.length =
      typeEntropy (goodDigitCount A (sourceCell D P timeClass)
        (sourceGood D P chi) y z x) / Real.log (D.N : ℝ) := by
  classical
  have hnormalized {d k : ℕ} (n : Fin d → Fin k → ℕ) (L : ℝ) (hL : 0 < L) :
      (∑ a, ∑ l,
        if 0 < (n a l : ℝ) / L then
          ((n a l : ℝ) / L) * Real.log ((∑ q, (n a q : ℝ) / L) / ((n a l : ℝ) / L))
        else 0) = typeEntropy n / L := by
    have hterm (a : Fin d) (l : Fin k) :
        (if 0 < (n a l : ℝ) / L then
          ((n a l : ℝ) / L) * Real.log ((∑ q, (n a q : ℝ) / L) / ((n a l : ℝ) / L))
        else 0) =
          ((n a l : ℝ) * Real.log (∑ q, (n a q : ℝ)) -
            (n a l : ℝ) * Real.log (n a l : ℝ)) / L := by
      by_cases hn : n a l = 0
      · simp only [hn, Nat.cast_zero, zero_div, lt_self_iff_false, ↓reduceIte,
          zero_mul, sub_self]
      · have hnpos : (0 : ℝ) < n a l := by exact_mod_cast Nat.pos_of_ne_zero hn
        have htotal : (0 : ℝ) < ∑ q, (n a q : ℝ) :=
          hnpos.trans_le (Finset.single_le_sum
            (fun q _ => Nat.cast_nonneg (n a q)) (Finset.mem_univ l))
        rw [if_pos (div_pos hnpos hL), ← Finset.sum_div,
          div_div_div_cancel_right₀ (ne_of_gt hL),
          Real.log_div (ne_of_gt htotal) (ne_of_gt hnpos)]
        ring
    simp_rw [hterm, ← Finset.sum_div]
    unfold typeEntropy
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, Nat.cast_sum]
  have hN : (1 : ℝ) < D.N := by exact_mod_cast D.one_lt_N
  have hL : 0 < Real.log (D.N : ℝ) := Real.log_pos hN
  unfold TimeProfile.profileH TimeProfile.digitTotal
  simp_rw [digitCount_source_eq A P timeClass chi y z x hx]
  let n := goodDigitCount A (sourceCell D P timeClass) (sourceGood D P chi) y z x
  change (∑ a : Fin R × Fin P.cellCount, ∑ l : Fin D.k,
    if 0 < (n (finProdFinEquiv a) l : ℝ) / Real.log (D.N : ℝ) then
      ((n (finProdFinEquiv a) l : ℝ) / Real.log (D.N : ℝ)) *
        Real.log ((∑ q, (n (finProdFinEquiv a) q : ℝ) / Real.log (D.N : ℝ)) /
          ((n (finProdFinEquiv a) l : ℝ) / Real.log (D.N : ℝ))) else 0) =
    typeEntropy n / Real.log (D.N : ℝ)
  exact (finProdFinEquiv.sum_comp (fun a : Fin (R * P.cellCount) =>
    ∑ l : Fin D.k,
      if 0 < (n a l : ℝ) / Real.log (D.N : ℝ) then
        ((n a l : ℝ) / Real.log (D.N : ℝ)) *
          Real.log ((∑ q, (n a q : ℝ) / Real.log (D.N : ℝ)) /
            ((n a l : ℝ) / Real.log (D.N : ℝ))) else 0)).trans
    (hnormalized n (Real.log (D.N : ℝ)) hL)

theorem profileWord_profileR_le (A : Riffle.Setup D)
    (P : TimeProfile.BorelPartition D.k) (chi alpha : ℝ)
    (p : ProfileWord A (sourceGood D P chi) alpha) :
    TimeProfile.profileR D.N (asProfile D)
      (legalVector p.val.2.2
        (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
          p.property.2.1).1)
      P chi (Riffle.join p.val.1 p.val.2.1).length p.val.2.2.length ≤ alpha := by
  rw [profileR_source_eq A P chi]
  have hN : (1 : ℝ) < D.N := by exact_mod_cast D.one_lt_N
  exact (div_le_iff₀ (Real.log_pos hN)).mpr p.property.2.2

theorem profileWord_profileH_key (A : Riffle.Setup D)
    (P : TimeProfile.BorelPartition D.k) (timeClass : Fin D.K → Fin R)
    (chi alpha : ℝ)
    (route : ProfileWord A (sourceGood D P chi) alpha → Fin 4)
    (p : ProfileWord A (sourceGood D P chi) alpha) :
    TimeProfile.profileH D.N (asProfile D)
      (legalVector p.val.2.2
        (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
          p.property.2.1).1)
      P timeClass chi (Riffle.join p.val.1 p.val.2.1).length p.val.2.2.length =
      typeEntropy (profileKeyCounts (c := R * P.cellCount)
        (encodeProfile A (sourceCell D P timeClass) (sourceGood D P chi) alpha route p)) /
        Real.log (D.N : ℝ) := by
  rw [profileKeyCounts_encode, profileH_source_eq A P timeClass chi]

theorem profileFibre_card_le_rpow_profileH (A : Riffle.Setup D)
    (P : TimeProfile.BorelPartition D.k) (timeClass : Fin D.K → Fin R)
    (chi alpha : ℝ)
    (route : ProfileWord A (sourceGood D P chi) alpha → Fin 4)
    (p : ProfileWord A (sourceGood D P chi) alpha) :
    (Nat.card (ProfileFibre A (sourceCell D P timeClass) (sourceGood D P chi)
      alpha route
        (encodeProfile A (sourceCell D P timeClass) (sourceGood D P chi) alpha route p)) : ℝ) ≤
      (D.N : ℝ) ^ (TimeProfile.profileH D.N (asProfile D)
        (legalVector p.val.2.2
          (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
            p.property.2.1).1)
        P timeClass chi (Riffle.join p.val.1 p.val.2.1).length p.val.2.2.length) := by
  rw [profileWord_profileH_key A P timeClass chi alpha route p]
  exact profileFibre_card_le_rpow_entropy A (sourceCell D P timeClass)
    (sourceGood D P chi) alpha route _

end

end InhomogeneousShuffle.FirstMoment.Model
