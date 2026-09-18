import RiffleProfiles.Estimates
import RiffleTimeProfile.Ambient

/-! S01–S03: applications of the frozen finite estimates to existing source definitions. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace RiffleProfiles

variable {k K : ℕ}

theorem source_digitCost_eq_cost (z : ℝ) : TimeProfile.digitCost z = cost z := by
  simp only [TimeProfile.digitCost, cost, one_div, Real.log_inv]

theorem source_regularDigits (J : Finset (Fin K))
    (p : Fin K → TimeProfile.Simplex k) (x : Fin K → Fin k)
    (P : TimeProfile.BorelPartition k) {χ C : ℝ} (hχ : 0 < χ)
    (hreg : P.IsRegular χ C) :
    RegularDigits J (fun j => TimeProfile.prob (p j) (x j))
      (fun j => TimeProfile.prob (P.rep (P.classify (p j))) (x j)) χ (C * χ) := by
  refine ⟨hχ, ?_, ?_⟩
  · intro j _hj hgood
    simpa only [source_digitCost_eq_cost] using
      hreg.good_digit (P.classify (p j)) (p j) (x j) rfl hgood
  · intro j _hj hbad
    exact hreg.exceptional_digit (P.classify (p j)) (p j) (x j) rfl hbad

theorem source_cE_replacement (N M : ℕ) (p : Fin K → TimeProfile.Simplex k)
    (P : TimeProfile.BorelPartition k) (χ C : ℝ)
    (m δ : Fin P.cellCount → ℝ) (hN : 2 ≤ N) (hreg : P.IsRegular χ C)
    (hcount : ∀ i,
      |(((TimeProfile.positions K M K).filter fun j => P.classify (p j) = i).card : ℝ) /
          TimeProfile.logScale N - m i| ≤ δ i) :
    |TimeProfile.cE N p M + ∑ i, m i * TimeProfile.psi (P.rep i) 2| ≤
      ((TimeProfile.positions K M K).card : ℝ) * C * χ / TimeProfile.logScale N +
        ∑ i, |TimeProfile.psi (P.rep i) 2| * δ i := by
  have h := tail_cell_replacement (TimeProfile.positions K M K)
    (fun j => P.classify (p j)) (fun j => TimeProfile.psi (p j) 2)
    (fun i => TimeProfile.psi (P.rep i) 2) m δ (TimeProfile.logScale_pos hN)
    (fun j _hj => hreg.psi_rep_error (p j) (by norm_num))
    hcount
  have heq : -normalizedSum (TimeProfile.positions K M K)
      (fun j => TimeProfile.psi (p j) 2) (TimeProfile.logScale N) -
      (-(∑ i, m i * TimeProfile.psi (P.rep i) 2)) =
      TimeProfile.cE N p M + ∑ i, m i * TimeProfile.psi (P.rep i) 2 := by
    unfold normalizedSum TimeProfile.cE
    ring
  rw [heq] at h
  simpa only [mul_assoc] using h

theorem source_cL_maximal_target (N w M : ℕ)
    (p : Fin K → TimeProfile.Simplex k) (x : Fin K → Fin k)
    (P : TimeProfile.BorelPartition k) (χ C b : ℝ)
    (m δ : Fin P.cellCount → ℝ) (hN : 2 ≤ N) (hreg : P.IsRegular χ C)
    (hlegal : TimeProfile.LegalPrefix p x M)
    (hcount : ∀ i,
      |(((TimeProfile.positions K w M).filter fun j => P.classify (p j) = i).card : ℝ) /
          TimeProfile.logScale N - m i| ≤ δ i) :
    TimeProfile.cL N p x b w M ≤ b - ∑ i, m i * TimeProfile.maxCost (P.rep i) +
      (((TimeProfile.positions K w M).card : ℝ) * C * χ / TimeProfile.logScale N +
        ∑ i, |TimeProfile.maxCost (P.rep i)| * δ i) := by
  have hmax : TimeProfile.cL N p x b w M ≤ b -
      normalizedSum (TimeProfile.positions K w M) (fun j => TimeProfile.maxCost (p j))
        (TimeProfile.logScale N) := by
    have h := maximal_pile_domination (TimeProfile.positions K w M)
      (fun j => TimeProfile.prob (p j) (x j)) (fun j => TimeProfile.pileMax (p j)) b
      (TimeProfile.logScale_pos hN)
      (fun j hj => hlegal j (Finset.mem_filter.mp hj).2.2)
      (fun j _hj => TimeProfile.prob_le_pileMax (p j) (x j))
    simpa only [TimeProfile.cL, TimeProfile.maxCost, source_digitCost_eq_cost,
      lengthExponent, normalizedSum] using h
  have herr := cell_replacement (TimeProfile.positions K w M)
    (fun j => P.classify (p j)) (fun j => TimeProfile.maxCost (p j))
    (fun i => TimeProfile.maxCost (P.rep i)) m δ (TimeProfile.logScale_pos hN)
    (fun j _hj => hreg.maxCost_rep_error (p j)) hcount
  simpa only [mul_assoc] using maximal_pile_target hmax herr

end RiffleProfiles
