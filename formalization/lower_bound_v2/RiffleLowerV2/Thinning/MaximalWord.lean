import Contracts.v1.AssemblyInputs
import RiffleLowerV2.Shared.Adapters

noncomputable section
open scoped BigOperators NNReal
namespace RiffleLowerV2.Thinning
open TimeProfile Targets

private theorem exists_least_maximizer {k : ℕ} (f : Fin k → ℕ)
    (hne : Nonempty (Fin k)) :
    ∃ a : Fin k, (∀ l, f l ≤ f a) ∧ (∀ l, f l = f a → a ≤ l) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ f
    (Finset.univ_nonempty_iff.mpr hne)
  let S := Finset.univ.filter fun a => ∀ l, f l ≤ f a
  have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    fun l => ha l (Finset.mem_univ _)⟩⟩
  refine ⟨S.min' hS, (Finset.mem_filter.mp (S.min'_mem hS)).2, ?_⟩
  intro l hl
  apply Finset.min'_le
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro a
  rw [hl]
  exact (Finset.mem_filter.mp (S.min'_mem hS)).2 a

/-- Choose the smallest maximizing digit before sampling; all feasible alphabets are allowed. -/
theorem exists_canonicalMaxWord {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) :
    ∃ w : Word k K, IsCanonicalMaxWord cuts w := by
  classical
  have h : ∀ j : Fin K, ∃ a : Fin k,
      (∀ l, cuts.count j l ≤ cuts.count j a) ∧
      (∀ l, cuts.count j l = cuts.count j a → a ≤ l) := by
    intro j
    obtain ⟨a, _⟩ := exists_prob_pos (cuts.profile hN j)
    exact exists_least_maximizer (cuts.count j) ⟨a⟩
  choose a ha using h
  refine ⟨List.Vector.ofFn a, ?_⟩
  intro j
  simpa only [List.Vector.get_ofFn] using ha j

/-- Every canonical maximizing word has exactly the product of the maximal pile fractions. -/
theorem canonicalMaxWord_mean {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (w : Word k K) (hw : IsCanonicalMaxWord cuts w) :
    (N : ℝ) * wordMass cuts w = maximalMean cuts hN := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmax (j : Fin K) : pileMax (cuts.profile hN j) =
      (cuts.count j (w.get j) : ℝ) / N := by
    apply le_antisymm
    · unfold pileMax
      have hp : ∀ l, prob (cuts.profile hN j) l ≤
          (cuts.count j (w.get j) : ℝ) / N := by
        intro l
        exact div_le_div_of_nonneg_right (by exact_mod_cast (hw j).1 l) hNr.le
      exact_mod_cast (Finset.sup_le (s := Finset.univ)
        (f := fun l : Fin k => (⟨prob (cuts.profile hN j) l, prob_nonneg _ _⟩ : ℝ≥0))
        (a := (⟨(cuts.count j (w.get j) : ℝ) / N, by positivity⟩ : ℝ≥0))
        (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) =>
          (show (⟨prob (cuts.profile hN j) l, prob_nonneg _ _⟩ : ℝ≥0) ≤
            (⟨(cuts.count j (w.get j) : ℝ) / N, by positivity⟩ : ℝ≥0) from hp l)))
    · exact prob_le_pileMax (cuts.profile hN j) (w.get j)
  unfold wordMass prefixMass fullPrefix maximalMean
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact (hmax j).symm

/-- Exact empirical horizon identity, with no temporal regularity assumptions. -/
theorem maximalMean_eq_rpow_beta {k N K : ℕ} (hN : 2 ≤ N) (cuts : Cuts k N K) :
    maximalMean cuts (deckPos hN) =
      (N : ℝ) ^ (beta cuts (deckPos hN) (horizon N K)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (deckPos hN)
  have hL : logScale N ≠ 0 := (logScale_pos hN).ne'
  have hp : 0 < ∏ j, pileMax (cuts.profile (deckPos hN) j) :=
    Finset.prod_pos fun j _ => pileMax_pos _
  have hA : A cuts (deckPos hN) 0 (horizon N K) =
      (∑ j, maxCost (cuts.profile (deckPos hN) j)) / logScale N := by
    have hg := empiricalIntegral_grid hN
      (fun j => maxCost (cuts.profile (deckPos hN) j)) 0 K (Nat.zero_le _)
    simpa [A, horizon, gridTime, gridSum] using hg
  rw [Real.rpow_def_of_pos hNr]
  apply (Real.log_injOn_pos (mul_pos hNr hp) (Real.exp_pos _))
  rw [Real.log_exp, Real.log_mul hNr.ne' hp.ne']
  rw [Real.log_prod (fun j _ => (pileMax_pos (cuts.profile (deckPos hN) j)).ne')]
  rw [beta, hA]
  simp only [maxCost, digitCost, one_div, Real.log_inv, Finset.sum_neg_distrib]
  change _ = logScale N * _
  field_simp [hL]
  dsimp [logScale]
  ring

/-- Frozen LB-02 maximal-word identity, including the canonical tie rule. -/
theorem maximalMeanIdentity : Targets.MaximalMeanIdentity := by
  intro k N K _ hN cuts
  obtain ⟨w, hw⟩ := exists_canonicalMaxWord cuts (deckPos hN)
  exact ⟨w, hw, canonicalMaxWord_mean cuts (deckPos hN) w hw,
    maximalMean_eq_rpow_beta hN cuts⟩

end RiffleLowerV2.Thinning
