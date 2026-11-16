import RiffleUpperV2.FirstMoment.AnchoredCosts
import RiffleUpperV2.FirstMoment.FirstColumn

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric

/-- Prefix probability as the selected full-population product. -/
theorem prefixMass_selected_product {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (default : Fin d → Fin k) (x : Prefix k d) :
    prefixMass cuts x = ∏ j ∈ empiricalPositions d 0 0 x.1.val,
      prob (cuts.profile hn j) (completePrefix default x j) := by
  let root : Prefix k d := ⟨⟨0,by omega⟩,RiffleShuffle.emptyWord k⟩
  have hp : IsPrefix root x := by exact List.nil_prefix
  have h := prefixMass_extension cuts hn default hp
  have hroot : prefixMass cuts root = 1 := by
    simp [root,prefixMass,RiffleLowerV2.prefixMass]
  rw [hroot,one_mul] at h
  exact h

/-- The actual anchored prefix exponent is bounded by the current-array maximum-word
prefix exponent, still normalized by original log N. -/
theorem anchoredExponent_le_beta {k n d N : ℕ} (hN : 2 ≤ N) (a : ℕ)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    (default : Fin d → Fin k) (x : Prefix k d) (hx : Legal cuts R x) :
    meanExponent N cuts R x ≤ empiricalBeta N a cuts hn (a+x.1.val) := by
  let I := empiricalPositions d 0 0 x.1.val
  let w := completePrefix default x
  have hlegal : ∀ j ∈ I, 0 < prob (cuts.profile hn j) (w j) := by
    intro j hj
    exact legal_prefix_digits cuts hn R default x hx j
      (by simpa [I,empiricalPositions] using (Finset.mem_filter.mp hj).2.2)
  have hp : 0 < prefixMass cuts x := by
    rw [prefixMass_selected_product cuts hn default]
    exact Finset.prod_pos hlegal
  have hcard : (R.card : ℝ) ≤ n := by exact_mod_cast (show R.card ≤ n by simpa using Finset.card_le_univ R)
  have hmean : anchoredMean cuts R x ≤ (n : ℝ)*prefixMass cuts x :=
    mul_le_mul_of_nonneg_right hcard hp.le
  have hlog := div_le_div_of_nonneg_right (Real.log_le_log hx hmean) (logScale_pos hN).le
  have hcost : empiricalA N a cuts hn a (a+x.1.val) ≤ selectedCost N (cuts.profile hn) I w := by
    apply div_le_div_of_nonneg_right _ (logScale_pos hN).le
    simp only [Nat.sub_self,Nat.add_sub_cancel_left]
    change (∑ j ∈ I, maxCost (cuts.profile hn j)) ≤ _
    apply Finset.sum_le_sum
    intro j hj
    exact Real.log_le_log (one_div_pos.mpr (pileMax_pos _))
      (one_div_le_one_div_of_le (hlegal j hj) (prob_le_pileMax _ _))
  have hproduct := selectedCost_log_product (cuts.profile hn) I w hlegal (N := N)
  have hmass : prefixMass cuts x = ∏ j ∈ I, prob (cuts.profile hn j) (w j) :=
    prefixMass_selected_product cuts hn default x
  rw [← hmass,neg_div] at hproduct
  rw [Real.log_mul (by positivity : (n : ℝ) ≠ 0) hp.ne',add_div] at hlog
  change meanExponent N cuts R x ≤ empiricalBeta N a cuts hn (a+x.1.val)
  unfold empiricalBeta
  change meanExponent N cuts R x ≤ Real.log (n : ℝ)/logScale N - _
  change meanExponent N cuts R x ≤ Real.log (n : ℝ)/logScale N + Real.log (prefixMass cuts x)/logScale N at hlog
  linarith

/-- Reattach the already exposed pile digit only for comparison with the original
array's cost; all localization objects remain future-only. -/
def anchorPrefix {k d : ℕ} (a : Fin k) (x : Prefix k d) : Prefix k (d+1) :=
  ⟨⟨x.1.val+1,by have := x.1.isLt; omega⟩,List.Vector.cons a x.2⟩

/-- Exact first-pile mass factorization, with no replacement of the future population. -/
theorem anchorPrefix_mass {k n d : ℕ} (cuts : Cuts k n (d+1))
    (a : Fin k) (x : Prefix k d) :
    prefixMass cuts (anchorPrefix a x) = (cuts.count 0 a : ℝ)/n * prefixMass (tailCuts cuts) x := by
  unfold RiffleUpperV2.prefixMass RiffleLowerV2.prefixMass anchorPrefix
  rw [Fin.prod_univ_succ]
  congr 1

theorem firstPile_anchoredMean {k n d : ℕ} (cuts : Cuts k n (d+1)) (hn : 0 < n)
    (c : ColumnAssignments cuts 0) (a : Fin k) (x : Prefix k d) :
    anchoredMean (tailCuts cuts) (anchorRows c a) x =
      anchoredMean cuts Finset.univ (anchorPrefix a x) := by
  unfold anchoredMean
  rw [anchorRows_card,Finset.card_univ,Fintype.card_fin,anchorPrefix_mass]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The actual post-exposure join obeys the original-array beta bound, including
its exposed anchor cost and without using log of the pile size as a new scale. -/
theorem firstPileExponent_le_beta {k n d N : ℕ} (hN : 2 ≤ N) (a₀ : ℕ)
    (cuts : Cuts k n (d+1)) (hn : 0 < n) (c : ColumnAssignments cuts 0)
    (a : Fin k) (x : Prefix k d) (hx : Legal (tailCuts cuts) (anchorRows c a) x) :
    meanExponent N (tailCuts cuts) (anchorRows c a) x ≤
      empiricalBeta N a₀ cuts hn (a₀+1+x.1.val) := by
  have hmean := firstPile_anchoredMean cuts hn c a x
  have hlegal : Legal cuts Finset.univ (anchorPrefix a x) := by
    change 0 < anchoredMean cuts Finset.univ (anchorPrefix a x)
    rwa [← hmean]
  have h := anchoredExponent_le_beta hN a₀ cuts hn Finset.univ (fun _ => a) (anchorPrefix a x) hlegal
  change Real.log (anchoredMean (tailCuts cuts) (anchorRows c a) x)/logScale N ≤ _
  rw [hmean]
  simpa [meanExponent,normalizedExponent,anchorPrefix,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,logScale] using h

/-- Terminal control for every actual full future word follows from the original
array's terminal margin, including arbitrarily small positive first piles. -/
theorem firstPileTerminalExponent {k n d N : ℕ} (hN : 2 ≤ N) (a₀ : ℕ)
    (cuts : Cuts k n (d+1)) (hn : 0 < n) (c : ColumnAssignments cuts 0)
    (a : Fin k) (x : Prefix k d) (hx : Legal (tailCuts cuts) (anchorRows c a) x)
    (hfull : x.1.val = d) {eta : ℝ}
    (hterminal : empiricalBeta N a₀ cuts hn (a₀+(d+1)) ≤ -eta) :
    meanExponent N (tailCuts cuts) (anchorRows c a) x ≤ -eta := by
  apply (firstPileExponent_le_beta hN a₀ cuts hn c a x hx).trans
  simpa [hfull,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hterminal

end RiffleUpperV2.FirstMoment
