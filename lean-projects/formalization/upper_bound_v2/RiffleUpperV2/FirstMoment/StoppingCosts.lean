import RiffleUpperV2.FirstMoment.AnchoredCosts

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization

/-- Adding the final selected column adds at most one good-digit cost. The rare
final digit, if any, contributes zero to the left-hand side. -/
theorem goodCost_le_previousSelected {k d N : ℕ} (hN : 2 ≤ N)
    (p : Fin d → Simplex k) (w : Fin d → Fin k) (s u : ℕ)
    (hu : 0 < u) (hud : u ≤ d) (chi : ℝ) (hchi : 0 < chi) (hchi1 : chi ≤ 1)
    (hlegal : ∀ j ∈ empiricalPositions d 0 s u, 0 < prob (p j) (w j)) :
    goodCost N p (empiricalPositions d 0 s u) chi w ≤
      selectedCost N p (empiricalPositions d 0 s (u-1)) w + crossingPenalty N chi := by
  classical
  let I := empiricalPositions d 0 s u
  let J := empiricalPositions d 0 s (u-1)
  let G := goodPositions p I chi w
  let last : Fin d := ⟨u-1,by omega⟩
  have hJ (j : Fin d) (hj : j ∈ J) : j ∈ I := by
    simp only [J,I,empiricalPositions,Finset.mem_filter,Finset.mem_univ,true_and,Nat.sub_zero] at hj ⊢
    omega
  have hlog : 0 ≤ Real.log (1/chi) := Real.log_nonneg ((one_le_div hchi).mpr hchi1)
  let f := fun j : Fin d => (if j ∈ J then digitCost (prob (p j) (w j)) else 0) +
    (if j = last then Real.log (1/chi) else 0)
  have hf (j : Fin d) : 0 ≤ f j := by
    apply add_nonneg
    · split_ifs with hj
      · exact Real.log_nonneg ((one_le_div (hlegal j (hJ j hj))).mpr (prob_le_one _ _))
      · exact le_rfl
    · split_ifs <;> positivity
  have hs : (∑ j ∈ G, digitCost (prob (p j) (w j))) ≤ ∑ j, f j := by
    apply (Finset.sum_le_sum ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G) (fun j _ _ => hf j))
    intro j hj
    have hjI := (Finset.mem_sdiff.mp hj).1
    have hjgood : chi ≤ prob (p j) (w j) := by
      have h := (Finset.mem_sdiff.mp hj).2
      simpa [exceptionalPositions,hjI] using h
    by_cases hjJ : j ∈ J
    · dsimp [f]
      simp only [hjJ,if_true]
      exact le_add_of_nonneg_right (by split_ifs <;> positivity)
    · have hjlast : j = last := by
        apply Fin.ext
        have hh : s ≤ j.val ∧ j.val < u := by simpa [I,empiricalPositions] using hjI
        have hn : ¬(s ≤ j.val ∧ j.val < u-1) := by simpa [J,empiricalPositions] using hjJ
        dsimp [last]
        omega
      dsimp [f]
      rw [if_neg hjJ,if_pos hjlast,zero_add]
      exact Real.log_le_log (one_div_pos.mpr (hchi.trans_le hjgood))
        (one_div_le_one_div_of_le hchi hjgood)
  have hsum : (∑ j, f j) = (∑ j ∈ J, digitCost (prob (p j) (w j)))+Real.log (1/chi) := by
    simp [f,Finset.sum_add_distrib,← Finset.sum_filter]
  rw [hsum] at hs
  have h := div_le_div_of_nonneg_right hs (logScale_pos hN).le
  simpa only [goodCost,selectedCost,G,I,J,add_div,crossingPenalty,logScale] using h

/-- The proper-stop parent test gives the manuscript's repaired good-cost bound
for the actual selected word. -/
theorem properStable_goodCost {k n d N : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    (default : Fin d → Fin k) (v x : Prefix k d) (delta chi : ℝ)
    (hdelta : 0 ≤ delta) (hchi : 0 < chi) (hchi1 : chi ≤ 1)
    (hx : ProperStable N cuts R v delta x) :
    goodCost N (cuts.profile hn) (empiricalPositions d 0 v.1.val x.1.val) chi
      (completePrefix default x) ≤ meanExponent N cuts R v - boundaryFluctuation N cuts R v +
        crossingPenalty N chi := by
  have hxpos : 0 < x.1.val := lt_of_le_of_lt (Nat.zero_le _) hx.2.1
  have hp := (proper_parent_not_stopped hx).1
  have hpx : IsPrefix (parent x) x := takePrefix_isPrefix _ _ _
  have hplegal := legal_prefix cuts hn R hx.1.1 hpx
  have hbound := goodCost_le_previousSelected hN (cuts.profile hn) (completePrefix default x)
    v.1.val x.1.val hxpos (Nat.le_of_lt_succ x.1.isLt) chi hchi hchi1
    (fun j hj => legal_prefix_digits cuts hn R default x hx.1.1 j
      (by simpa [empiricalPositions] using (Finset.mem_filter.mp hj).2.2))
  have heq : selectedCost N (cuts.profile hn) (empiricalPositions d 0 v.1.val (x.1.val-1))
      (completePrefix default x) =
    selectedCost N (cuts.profile hn) (empiricalPositions d 0 v.1.val (parent x).1.val)
      (completePrefix default (parent x)) := by
    unfold selectedCost
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j.val < (parent x).1.val := by
      simpa [empiricalPositions,parent] using (Finset.mem_filter.mp hj).2.2
    have hjx : j.val < x.1.val := lt_of_lt_of_le hjp (prefix_length_le hpx)
    have hget : (parent x).2.get ⟨j.val,hjp⟩ = x.2.get ⟨j.val,hjx⟩ := by
      simpa [List.Vector.get,List.Vector.toList] using hpx.getElem (by simpa using hjp)
    simp [completePrefix,hjp,hjx,hget]
  rw [heq,selectedCost_split] at hbound
  have hsplit := anchoredExactCostSplit cuts hn R default hp hplegal chi (N := N)
  have hparent := proper_parent_exponent hx
  linarith

end RiffleUpperV2.FirstMoment
