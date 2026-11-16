import RiffleLowerV2.Factorial.Ratios

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiffleLowerV2.Factorial
open TimeProfile

def numericalMean {K : ℕ} (M : ℝ) (n : Fin K → ℝ) : ℝ := M * ∏ j, n j / M

theorem numericalMean_pos {K : ℕ} {M : ℝ} {n : Fin K → ℝ}
    (hM : 0 < M) (hn : ∀ j, 0 < n j) : 0 < numericalMean M n :=
  mul_pos hM (Finset.prod_pos fun j _ => div_pos (hn j) hM)

theorem log_numericalMean {K : ℕ} {M : ℝ} {n : Fin K → ℝ}
    (hM : 0 < M) (hn : ∀ j, 0 < n j) :
    Real.log (numericalMean M n) = Real.log M + ∑ j, (Real.log (n j) - Real.log M) := by
  rw [numericalMean, Real.log_mul hM.ne' (Finset.prod_pos fun j _ => div_pos (hn j) hM).ne',
    Real.log_prod (fun j _ => (div_pos (hn j) hM).ne')]
  simp_rw [Real.log_div (hn _).ne' hM.ne']

theorem numericalMean_log_ratio_bound {K : ℕ} {M M' : ℝ} {n n' : Fin K → ℝ}
    (hM : 0 < M) (hM' : 0 < M') (hn : ∀ j, 0 < n j) (hn' : ∀ j, 0 < n' j)
    {a b : ℝ} (hpop : |Real.log (M'/M)| ≤ b)
    (hpile : ∀ j, |Real.log (n' j/n j)| ≤ a) :
    |Real.log (numericalMean M' n' / numericalMean M n)| ≤ b + K*(a+b) := by
  have hpop' : |Real.log M' - Real.log M| ≤ b := by
    simpa [Real.log_div hM'.ne' hM.ne'] using hpop
  have hpile' (j) : |Real.log (n' j) - Real.log (n j)| ≤ a := by
    simpa [Real.log_div (hn' j).ne' (hn j).ne'] using hpile j
  rw [Real.log_div (numericalMean_pos hM' hn').ne' (numericalMean_pos hM hn).ne',
    log_numericalMean hM' hn', log_numericalMean hM hn]
  have heq : Real.log M' + ∑ j, (Real.log (n' j) - Real.log M') -
      (Real.log M + ∑ j, (Real.log (n j) - Real.log M)) =
      (Real.log M' - Real.log M) +
      ∑ j, ((Real.log (n' j) - Real.log (n j)) - (Real.log M' - Real.log M)) := by
    simp only [Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |Real.log M' - Real.log M| +
        |∑ j, ((Real.log (n' j) - Real.log (n j)) - (Real.log M' - Real.log M))| := abs_add_le _ _
    _ ≤ b + ∑ j, |(Real.log (n' j) - Real.log (n j)) - (Real.log M' - Real.log M)| :=
      add_le_add hpop' (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ b + ∑ _j : Fin K, (a+b) := by
      gcongr with j
      exact (abs_sub _ _).trans (add_le_add (hpile' j) hpop')
    _ = b + K*(a+b) := by simp; ring

theorem usedCount_le {N k K b : ℕ} (p : RowPrescription N k K b) (j : Fin K) (a : Fin k) :
    usedCount p j a ≤ b := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem wordMean_eq_numericalMean {N k K : ℕ} (cuts : Cuts k N K) (w : Word k K) :
    (N : ℝ) * wordMass cuts w = numericalMean N (fun j => (cuts.count j (w.get j) : ℝ)) := by
  rfl

/-- A finite residual mean estimate with the population and pile budgets visible. -/
theorem residualMean_finite {N k K b : ℕ} (cuts : Cuts k N K)
    (p : RowPrescription N k K b) (w : Word k K) {c : ℝ}
    (hc : 0 < c) (hN : 0 < N) (hb : 2*b ≤ N)
    (hbc : 2*(b : ℝ) ≤ c*N)
    (hpiles : ∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ))
    (he : 2*(1+1/c)*(K+1)*b/N ≤ (1 : ℝ)) :
    |Targets.residualWordMean cuts p w - (N : ℝ)*wordMass cuts w| ≤
      (4*(1+1/c))*(K+1)*b/N * ((N : ℝ)*wordMass cuts w) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbN : b < N := by omega
  have hN' : (0 : ℝ) < (N-b : ℕ) := by exact_mod_cast (show 0 < N-b by omega)
  let n : Fin K → ℝ := fun j => cuts.count j (w.get j)
  let n' : Fin K → ℝ := fun j => (cuts.count j (w.get j) - usedCount p j (w.get j) : ℕ)
  have hn (j : Fin K) : 0 < n j := lt_of_lt_of_le (mul_pos hc hNr) (hpiles j)
  have hu (j : Fin K) : 2*usedCount p j (w.get j) ≤ cuts.count j (w.get j) := by
    have huR : (usedCount p j (w.get j) : ℝ) ≤ b := by exact_mod_cast usedCount_le p j (w.get j)
    have hh : (2 : ℝ)*usedCount p j (w.get j) ≤ cuts.count j (w.get j) :=
      (by nlinarith : (2 : ℝ)*usedCount p j (w.get j) ≤ c*N).trans (hpiles j)
    exact_mod_cast hh
  have hn' (j : Fin K) : 0 < n' j := by
    have hh : 0 < cuts.count j (w.get j) := by
      have : (0 : ℝ) < cuts.count j (w.get j) := hn j
      exact_mod_cast this
    have := hu j
    change (0 : ℝ) < ((cuts.count j (w.get j) - usedCount p j (w.get j) : ℕ) : ℝ)
    exact_mod_cast (show 0 < cuts.count j (w.get j) - usedCount p j (w.get j) by omega)
  have hlogN : |Real.log (((N-b : ℕ) : ℝ)/(N : ℝ))| ≤ 2*(b : ℝ)/N :=
    log_sub_ratio_bound hN hb
  have hlogn (j : Fin K) : |Real.log (n' j/n j)| ≤ 2*(b : ℝ)/(c*N) := by
    have hnNat : 0 < cuts.count j (w.get j) := by
      have : (0 : ℝ) < cuts.count j (w.get j) := hn j
      exact_mod_cast this
    have hh := log_sub_ratio_bound hnNat (hu j)
    apply hh.trans
    apply div_le_div₀ (by positivity) (by exact_mod_cast (Nat.mul_le_mul_left 2 (usedCount_le p j (w.get j))))
      (mul_pos hc hNr) (hpiles j)
  have hlog := numericalMean_log_ratio_bound hNr hN' hn hn' hlogN hlogn
  have hbudget : 2*(b : ℝ)/N + (K : ℝ)*(2*b/(c*N)+2*b/N) ≤
      2*(1+1/c)*(K+1)*b/N := by
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) b]
  have hfin := relative_error_of_log (numericalMean_pos hN' hn') (numericalMean_pos hNr hn)
    (hlog.trans hbudget) he
  rw [wordMean_eq_numericalMean]
  change |numericalMean (N-b : ℕ) n' - numericalMean N n| ≤ _
  convert hfin using 1 <;> ring

theorem residualBudget_tendsto (c C : ℝ) (b0 : ℕ) :
    Tendsto (fun N : ℕ => 2*(1+1/c)*(C*logScale N+1)*b0/N) atTop (𝓝 0) := by
  have ha : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hb : Tendsto (fun x : ℝ => (1 : ℝ)/x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hh := (((ha.const_mul C).add hb).const_mul (2*(1+1/c)*b0)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert hh using 1
  · ext N
    dsimp [logScale]
    ring
  · ring

/-- Frozen residual mean comparison, with its complete uniform quantifier order. -/
theorem residualMeanComparison : Targets.ResidualMeanComparison := by
  intro c C hc hC b0
  have hD : 0 < 4*(1+1/c) := by positivity
  have hev := (residualBudget_tendsto c C b0).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  let N0 := max N1 (max (2*b0+2) ⌈2*(b0 : ℝ)/c⌉₊)
  have hb0N0 : b0 < N0 := by dsimp [N0]; omega
  have hN02 : 2 ≤ N0 := by dsimp [N0]; omega
  refine ⟨4*(1+1/c), hD, N0, hb0N0, hN02, ?_⟩
  intro N hN k K b hb hK cuts p w _ _ hpiles
  have hNN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hNN2 : 2*b0+2 ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hNceil : ⌈2*(b0 : ℝ)/c⌉₊ ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbc0 : 2*(b0 : ℝ) ≤ c*N := by
    have hh : 2*(b0 : ℝ)/c ≤ (N : ℝ) :=
      (Nat.le_ceil (2*(b0 : ℝ)/c)).trans (by exact_mod_cast hNceil)
    have := (div_le_iff₀ hc).mp hh
    nlinarith
  have hbR : (b : ℝ) ≤ b0 := by exact_mod_cast hb
  have he : 2*(1+1/c)*(K+1)*b/N ≤ (1 : ℝ) := by
    apply le_trans ?_ (hN1 N hNN1).le
    apply div_le_div_of_nonneg_right _ hNr.le
    apply mul_le_mul
    · gcongr
    · exact hbR
    · positivity
    · have : 0 ≤ C*logScale N+1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
      positivity
  exact residualMean_finite cuts p w hc (by omega) (by omega) (by nlinarith) hpiles he

end RiffleLowerV2.Factorial
