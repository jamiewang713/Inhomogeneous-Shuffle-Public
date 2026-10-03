import RiffleUpperV2.GraphOverlap.Truncation
import RiffleUpperV2.GraphOverlap.LargestComponent

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2 RiffleLowerV2.Model RiffleLowerV2.Factorial

theorem density_empty {N : ℕ} (σ : Permutation N) : density (∅ : PathEdges N) σ = 1 := by
  have hi (π : Permutation N) : BlockIncreasing (∅ : PathEdges N) π :=
    (blockIncreasing_iff_edges _ _).mpr (by simp)
  have hn := density_normalized (∅ : PathEdges N)
  have heq : density (∅ : PathEdges N) = fun _ => (componentFactorial (∅ : PathEdges N) : ℝ) := by
    funext π
    simp only [density, hi, ↓reduceIte]
  rw [heq, RiffleLowerV2.Model.expect_const] at hn
  rw [heq, hn]

theorem overlap_empty {N : ℕ} : overlap (∅ : PathEdges N) ∅ = 1 := by
  simp [overlap, density_empty, RiffleLowerV2.Model.expect_const]

theorem tv_le_nonempty_graph {k N K : ℕ} (cuts : Cuts k N K) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      probability (fixedCountPMF cuts) (fun ω => shuffleEdges ω ≠ ∅) := by
  have h := truncatedTV cuts (fun ω => shuffleEdges ω = ∅)
  have hp (ω ω' : Sample cuts) :
      (if shuffleEdges ω = ∅ ∧ shuffleEdges ω' = ∅ then
        overlap (shuffleEdges ω) (shuffleEdges ω') - 1 else 0) = 0 := by
    split_ifs with he
    · rw [he.1, he.2, overlap_empty, sub_self]
    · rfl
  simp only [RiffleUpperV2.expect] at h
  simpa +contextual [hp, overlap_empty, RiffleLowerV2.Model.expect_const] using h

theorem nonempty_graph_has_collision {k N K : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) (h : shuffleEdges ω ≠ ∅) :
    ∃ w : Word k K, 2 ≤ wordCount w ω := by
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr h
  have htie := (Finset.mem_filter.mp he).2
  let a := stableSort ω (edgeLeft e)
  let b := stableSort ω (edgeRight e)
  have hab : a ≠ b := by
    intro hh
    have hpos := congrArg Fin.val ((stableSort ω).injective hh)
    dsimp [edgeLeft, edgeRight] at hpos
    omega
  refine ⟨rowWord ω a, ?_⟩
  rw [wordCount_eq_card, Fintype.card_subtype]
  calc
    2 = ({a, b} : Finset (Fin N)).card := by simp [hab]
    _ ≤ (Finset.univ.filter fun i => rowWord ω i = rowWord ω a).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact htie.symm

theorem occupancyUnion_le_chooseMoment {Ω W : Type*} [Fintype Ω] [Fintype W]
    (P : PMF Ω) (X : W → Ω → ℕ) (q : ℕ) :
    RiffleLowerV2.probability P (fun ω => ∃ w, q ≤ X w ω) ≤
      ∑ w, RiffleLowerV2.expect P (fun ω => ((X w ω).choose q : ℝ)) := by
  rw [← expect_sum]
  unfold RiffleLowerV2.probability
  apply expect_mono
  intro ω
  split_ifs with h
  · obtain ⟨w, hw⟩ := h
    have hp : (1 : ℝ) ≤ (X w ω).choose q := by exact_mod_cast Nat.choose_pos hw
    exact hp.trans (Finset.single_le_sum (f := fun v => ((X v ω).choose q : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ w))
  · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem wordBinomialMoment {k N K : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (q : ℕ) (hq : q ≤ N) :
    RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => ((wordCount w ω).choose q : ℝ)) =
      (N.choose q : ℝ) * ∏ j, falling (cuts.count j (w.get j)) q / falling N q := by
  simp_rw [choose_eq_falling_div]
  rw [expect_div, wordFactorialMoment cuts w q hq]
  ring

/-- Direct finite collision bound with the exact fixed-column falling-factorial factors. -/
theorem collisionUpper {k N K : ℕ} (cuts : Cuts k N K) (hN : 2 ≤ N) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      (N.choose 2 : ℝ) * ∏ j, ∑ a : Fin k, falling (cuts.count j a) 2 / falling N 2 := by
  apply (tv_le_nonempty_graph cuts).trans
  have hmono : probability (fixedCountPMF cuts) (fun ω => shuffleEdges ω ≠ ∅) ≤
      probability (fixedCountPMF cuts) (fun ω => ∃ w : Word k K, 2 ≤ wordCount w ω) := by
    unfold RiffleUpperV2.probability RiffleLowerV2.probability
    apply expect_mono
    intro ω
    by_cases h : shuffleEdges ω ≠ ∅
    · simp [h, nonempty_graph_has_collision ω h]
    · simp only [h, ↓reduceIte]
      split_ifs <;> norm_num
  apply hmono.trans
  apply (occupancyUnion_le_chooseMoment (fixedCountPMF cuts) (fun w ω => wordCount w ω) 2).trans_eq
  simp_rw [wordBinomialMoment cuts _ 2 hN]
  rw [← Finset.mul_sum]
  congr 1
  have hs := (Equiv.vectorEquivFin (Fin k) K).sum_comp
    (fun w : Fin K → Fin k => ∏ j, falling (cuts.count j (w j)) 2 / falling N 2)
  change (∑ w : Word k K, ∏ j, falling (cuts.count j (w.get j)) 2 / falling N 2) = _ at hs
  rw [hs, Fintype.prod_sum]

theorem columnCollision_le_exp_cost {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (j : Fin K) :
    (∑ a : Fin k, falling (cuts.count j a) 2 / falling N 2) ≤
      Real.exp (-TimeProfile.psi (cuts.profile hN j) 2) := by
  have hpos : 0 < TimeProfile.powerSum (cuts.profile hN j) 2 := by
    obtain ⟨a, ha⟩ := TimeProfile.exists_prob_pos (cuts.profile hN j)
    apply lt_of_lt_of_le (Real.rpow_pos_of_pos ha 2)
    exact Finset.single_le_sum (fun b _ =>
      Real.rpow_nonneg (TimeProfile.prob_nonneg _ b) 2) (Finset.mem_univ a)
  calc
    _ ≤ ∑ a : Fin k, ((cuts.count j a : ℝ)/N)^2 :=
      Finset.sum_le_sum (fun a _ => descFactorial_ratio_le_pow (count_le_population cuts j a) 2)
    _ = TimeProfile.powerSum (cuts.profile hN j) 2 := by
      simp only [TimeProfile.powerSum, Real.rpow_two]
      rfl
    _ = _ := by rw [TimeProfile.psi, neg_neg, Real.exp_log hpos]

theorem collisionUpper_exponential {k N K : ℕ} (cuts : Cuts k N K) (hN : 2 ≤ N) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      (N.choose 2 : ℝ) * Real.exp (-(∑ j, TimeProfile.psi (cuts.profile (by omega) j) 2)) := by
  apply (collisionUpper cuts hN).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    (∏ j, ∑ a : Fin k, falling (cuts.count j a) 2 / falling N 2) ≤
        ∏ j, Real.exp (-TimeProfile.psi (cuts.profile (by omega) j) 2) := by
      apply Finset.prod_le_prod
      · intro j _
        exact Finset.sum_nonneg (fun _ _ => div_nonneg (falling_nonneg _ _) (falling_nonneg _ _))
      · intro j _
        exact columnCollision_le_exp_cost cuts (by omega) j
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem collisionUpper_polynomial {k N K : ℕ} (cuts : Cuts k N K) (hN : 2 ≤ N)
    (ζ : ℝ) (hcost : (2+ζ)*Real.log N ≤ ∑ j, TimeProfile.psi (cuts.profile (by omega) j) 2) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤ (N : ℝ)^(-ζ)/2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (collisionUpper_exponential cuts hN).trans
  have he : Real.exp (-(∑ j, TimeProfile.psi (cuts.profile (by omega) j) 2)) ≤
      (N : ℝ)^(-(2+ζ)) := by
    rw [Real.rpow_def_of_pos hNr]
    apply Real.exp_le_exp.mpr
    nlinarith [hcost]
  calc
    _ ≤ ((N : ℝ)^2/2) * (N : ℝ)^(-(2+ζ)) := by
      apply mul_le_mul _ he (Real.exp_pos _).le (by positivity)
      simpa using (Nat.choose_le_pow_div 2 N : (N.choose 2 : ℝ) ≤ (N : ℝ)^2/(2 : ℕ).factorial)
    _ = (N : ℝ)^(-ζ)/2 := by
      rw [div_mul_eq_mul_div]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_add hNr]
      congr 1
      norm_num

end RiffleUpperV2.GraphOverlap
