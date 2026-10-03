import RiffleUpperV2.Exploration.Positions
import RiffleUpperV2.Exploration.Regularity
import RiffleUpperV2.GraphOverlap.Collision

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open TimeProfile RiffleLowerV2 RiffleLowerV2.Model RiffleLowerV2.Factorial RiffleLowerV2.Thinning GraphOverlap

/-- A tie in the actual sorted pile supplies two distinct labels with the same word. -/
theorem pile_not_edgeFree_has_collision {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω : Sample cuts) (h : ¬ pileEdgeFree cuts p ω) :
    ∃ w : Word k (L+1), w.get 0 = p ∧ 2 ≤ wordCount w ω := by
  simp only [pileEdgeFree, not_forall, not_not] at h
  obtain ⟨e, he⟩ := h
  let u : Fin (pileSize cuts p) := ⟨e.val, by omega⟩
  let v : Fin (pileSize cuts p) := ⟨e.val+1, by omega⟩
  let a := stableSort ω (pilePosition cuts p .forward u)
  let b := stableSort ω (pilePosition cuts p .forward v)
  have hab : a ≠ b := by
    intro hh
    have hh' := congrArg Fin.val ((stableSort ω).injective hh)
    simp only [pilePosition, spatialIndex, u, v] at hh'
    omega
  refine ⟨rowWord ω a, pilePosition_firstDigit cuts p .forward u ω, ?_⟩
  rw [wordCount_eq_card, Fintype.card_subtype]
  calc
    2 = ({a,b} : Finset (Fin n)).card := by simp [hab]
    _ ≤ (Finset.univ.filter fun i => rowWord ω i = rowWord ω a).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm⟩

/-- The total mass of all full words in one fixed first-column pile. -/
theorem pileWordMass_sum {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (p : Fin k) :
    (∑ w ∈ Finset.univ.filter (fun w : Word k (L+1) => w.get 0 = p), wordMass cuts w) =
      (pileSize cuts p : ℝ)/n := by
  let W := Finset.univ.filter (fun w : Word k (L+1) => w.get 0 = p)
  have hc (ω : Sample cuts) : (∑ w ∈ W, wordCount w ω) = pileSize cuts p := by
    have hh := Finset.sum_card_fiberwise_eq_card_filter
      (s := (Finset.univ : Finset (Fin n))) (t := W) (g := rowWord ω)
    simp only [wordCount_eq_card, Fintype.card_subtype]
    rw [hh]
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, rowWord_get, sampleEntry]
    exact (ω 0).property p
  have hw (w : Word k (L+1)) :
      RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => (wordCount w ω : ℝ)) = n * wordMass cuts w := by
    have hh := wordFactorialMoment cuts w 1 hn
    simpa only [falling, Nat.descFactorial_one, Nat.cast_id, wordMass_eq_prod] using hh
  have he := congrArg (fun f : Sample cuts → ℝ => RiffleLowerV2.expect (fixedCountPMF cuts) f)
    (show (fun ω => ∑ w ∈ W, (wordCount w ω : ℝ)) = fun _ => (pileSize cuts p : ℝ) by
      funext ω; exact_mod_cast hc ω)
  rw [RiffleLowerV2.Model.expect_const] at he
  have hs : RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => ∑ w ∈ W, (wordCount w ω : ℝ)) =
      ∑ w ∈ W, RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => (wordCount w ω : ℝ)) := by
    unfold RiffleLowerV2.expect
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hs] at he
  simp_rw [hw] at he
  rw [← Finset.mul_sum] at he
  apply (eq_div_iff (by exact_mod_cast hn.ne')).mpr
  simpa only [mul_comm] using he

/-- Occupancy union bound restricted to a deterministic set of words. -/
theorem wordCollision_set_bound {k n K : ℕ} (cuts : Cuts k n K)
    (hn : 2 ≤ n) (W : Finset (Word k K)) :
    probability (fixedCountPMF cuts) (fun ω => ∃ w ∈ W, 2 ≤ wordCount w ω) ≤
      (n.choose 2 : ℝ) * ∑ w ∈ W, wordMass cuts w ^ 2 := by
  have hpoint (ω : Sample cuts) :
      (if ∃ w ∈ W, 2 ≤ wordCount w ω then (1:ℝ) else 0) ≤
        ∑ w ∈ W, ((wordCount w ω).choose 2 : ℝ) := by
    split_ifs with h
    · obtain ⟨w, hw, hq⟩ := h
      have hp : (1:ℝ) ≤ (wordCount w ω).choose 2 := by exact_mod_cast Nat.choose_pos hq
      exact hp.trans (Finset.single_le_sum (f := fun v => ((wordCount v ω).choose 2 : ℝ))
        (fun _ _ => Nat.cast_nonneg _) hw)
    · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  calc
    _ ≤ RiffleLowerV2.expect (fixedCountPMF cuts)
        (fun ω => ∑ w ∈ W, ((wordCount w ω).choose 2 : ℝ)) := by
      unfold RiffleUpperV2.probability RiffleLowerV2.probability
      apply RiffleLowerV2.Factorial.expect_mono
      intro ω
      convert hpoint ω using 1
      split_ifs <;> rfl
    _ = ∑ w ∈ W, RiffleLowerV2.expect (fixedCountPMF cuts)
        (fun ω => ((wordCount w ω).choose 2 : ℝ)) := by
      unfold RiffleLowerV2.expect
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ w ∈ W, (n.choose 2 : ℝ) * wordMass cuts w ^ 2 :=
      Finset.sum_le_sum (fun w _ => wordBinomialMoment_le cuts w 2 hn)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Finite small-pile failure, with the actual maximal full-word mean. -/
theorem smallPileFailure_mean {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 2 ≤ n) (ξ : ℝ) :
    probability (fixedCountPMF cuts) (fun ω => ∃ p,
      (pileSize cuts p : ℝ) < (n : ℝ)^ξ ∧ ¬ pileEdgeFree cuts p ω) ≤
        (k : ℝ)/2 * (n : ℝ)^ξ * maximalMean cuts (by omega) := by
  have hn0 : 0 < n := by omega
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hp (p : Fin k) (hsmall : (pileSize cuts p : ℝ) < (n : ℝ)^ξ) :
      probability (fixedCountPMF cuts) (fun ω => ¬ pileEdgeFree cuts p ω) ≤
        (n : ℝ)^ξ * maximalMean cuts hn0 / 2 := by
    let W := Finset.univ.filter (fun w : Word k (L+1) => w.get 0 = p)
    have hm : 0 ≤ maximalMean cuts hn0 :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun _ _ => pileMax_nonneg _))
    have hmono : probability (fixedCountPMF cuts) (fun ω => ¬ pileEdgeFree cuts p ω) ≤
        probability (fixedCountPMF cuts) (fun ω => ∃ w ∈ W, 2 ≤ wordCount w ω) := by
      apply probability_mono
      intro ω h
      obtain ⟨w, hw, hc⟩ := pile_not_edgeFree_has_collision cuts p ω h
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, hc⟩
    apply hmono.trans ((wordCollision_set_bound cuts hn W).trans ?_)
    have hs : (∑ w ∈ W, wordMass cuts w ^ 2) ≤
        maximalMean cuts hn0/n * ((pileSize cuts p : ℝ)/n) := by
      calc
        _ ≤ ∑ w ∈ W, (maximalMean cuts hn0/n) * wordMass cuts w := by
          apply Finset.sum_le_sum
          intro w _
          rw [pow_two]
          exact mul_le_mul_of_nonneg_right (wordMass_le_maximalMean_div cuts hn0 w) (wordMass_nonneg cuts w)
        _ = _ := by rw [← Finset.mul_sum, pileWordMass_sum cuts hn0]
    have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ)^2/2 := by
      simpa using (Nat.choose_le_pow_div 2 n : (n.choose 2 : ℝ) ≤ (n : ℝ)^2/(2:ℕ).factorial)
    calc
      _ ≤ ((n : ℝ)^2/2) * (maximalMean cuts hn0/n * ((pileSize cuts p : ℝ)/n)) :=
        mul_le_mul hchoose hs (Finset.sum_nonneg (fun w _ => sq_nonneg _)) (by positivity)
      _ = (pileSize cuts p : ℝ)*maximalMean cuts hn0/2 := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall.le hm) (by norm_num)
  calc
    _ ≤ ∑ p : Fin k, probability (fixedCountPMF cuts) (fun ω =>
        (pileSize cuts p : ℝ) < (n : ℝ)^ξ ∧ ¬ pileEdgeFree cuts p ω) := probability_iUnion_le _ _
    _ ≤ ∑ _p : Fin k, (n : ℝ)^ξ * maximalMean cuts hn0/2 := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hs : (pileSize cuts p : ℝ) < (n : ℝ)^ξ
      · simpa only [hs, true_and] using hp p hs
      · simp only [hs, false_and, RiffleUpperV2.probability, RiffleLowerV2.probability, if_false, RiffleLowerV2.Model.expect_const]
        exact div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun _ _ => pileMax_nonneg _)))) (by norm_num)
    _ = _ := by simp; ring

/-- The source small-pile rate follows directly from the terminal mean margin. -/
theorem smallPileFailure {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 2 ≤ n) (ξ η : ℝ)
    (hmean : maximalMean cuts (by omega) ≤ (n : ℝ)^(-η)) :
    probability (fixedCountPMF cuts) (fun ω => ∃ p,
      (pileSize cuts p : ℝ) < (n : ℝ)^ξ ∧ ¬ pileEdgeFree cuts p ω) ≤
        (k : ℝ)/2 * (n : ℝ)^(ξ-η) := by
  apply (smallPileFailure_mean cuts hn ξ).trans
  calc
    _ ≤ (k : ℝ)/2 * (n : ℝ)^ξ * (n : ℝ)^(-η) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast (show 0<n by omega))]
      congr 2 <;> ring

end RiffleUpperV2.Exploration
