import RiffleLowerV2.Occupancy.CentralModel
import RiffleLowerV2.Occupancy.Marginal
import RiffleLowerV2.Occupancy.RegimeAlgebra

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Topology
open Filter
namespace RiffleLowerV2.Occupancy
open TimeProfile

theorem eventual_nonrare_budgets (A : ℝ) :
    ∃ N0 : ℕ, ∀ N ≥ N0, 2 ≤ N ∧ tau N ≤ 1/16 ∧
      2*(N : ℝ)^(-1/20 : ℝ) ≤ 1/2 ∧
      A*(N : ℝ)^(-7/10 : ℝ) ≤ poissonBase^2*(tau N)^5 ∧
      2*(N : ℝ)^(-1/20 : ℝ) ≤ poissonBase*(tau N)^3/4 := by
  have ht := eventually_negative_rpow_le (by norm_num : (-1/100 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1/16)
  have hl := eventually_negative_rpow_le (by norm_num : (-1/20 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1/4)
  have hc := eventually_const_mul_rpow_le (A/poissonBase^2) (-7/10) (-5/100) (by norm_num)
  have he := eventually_const_mul_rpow_le (8/poissonBase) (-1/20) (-3/100) (by norm_num)
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp
    ((eventually_ge_atTop 2).and (ht.and (hl.and (hc.and he))))
  refine ⟨N0, ?_⟩
  intro N hN
  obtain ⟨hN2,htN,hlN,hcN,heN⟩ := hN0 N hN
  have hNp : 0 < N := by omega
  have hc' : A*(N : ℝ)^(-7/10 : ℝ) ≤ poissonBase^2*(tau N)^5 := by
    have hh : (A*(N : ℝ)^(-7/10 : ℝ))/poissonBase^2 ≤ (N : ℝ)^(-5/100 : ℝ) := by
      convert hcN using 1; ring
    have hhh := (div_le_iff₀ (sq_pos_of_pos poissonBase_pos)).mp hh
    rw [tau_pow hNp]
    norm_num
    nlinarith
  have he' : 2*(N : ℝ)^(-1/20 : ℝ) ≤ poissonBase*(tau N)^3/4 := by
    have hh : (8*(N : ℝ)^(-1/20 : ℝ))/poissonBase ≤ (N : ℝ)^(-3/100 : ℝ) := by
      convert heN using 1; ring
    have hhh := (div_le_iff₀ poissonBase_pos).mp hh
    rw [tau_pow hNp]
    norm_num
    nlinarith
  exact ⟨hN2, htN, by linarith, hc', he'⟩

theorem nonrare_probability_lower {N k K : ℕ} (cuts : Cuts k N K) (w : Word k K)
    (hN : 0 < N) (ht : tau N ≤ 1/16)
    (hμ : tau N < (N : ℝ)*wordMass cuts w)
    (herr : |probability (fixedCountPMF cuts) (collisionEvent w) -
      poissonCollision ((N : ℝ)*wordMass cuts w)| ≤
      8*tau N*poissonCollision ((N : ℝ)*wordMass cuts w)) :
    poissonBase*(tau N)^2/2 ≤ probability (fixedCountPMF cuts) (collisionEvent w) := by
  have hf := benchmark_lower_at_tau (tau_pos hN).le (by linarith) hμ
  have hf0 : 0 ≤ poissonCollision ((N : ℝ)*wordMass cuts w) :=
    (mul_nonneg poissonBase_pos.le (sq_nonneg _)).trans hf
  have he := (abs_le.mp herr).1
  have hh := mul_le_mul_of_nonneg_right ht hf0
  nlinarith

theorem large_word_complement {N k K : ℕ} (cuts : Cuts k N K) (w : Word k K)
    (hN : 0 < N) (hμ : centralBound N < (N : ℝ)*wordMass cuts w) :
    probability (fixedCountPMF cuts) (fun ω => ¬collisionEvent w ω) ≤
      2*(N : ℝ)^(-1/20 : ℝ) := by
  have htail := fullWord_empty_singleton_tail cuts hN w
  have he : Real.exp (-((N : ℝ)*wordMass cuts w)/2) ≤ Real.exp (-centralBound N/2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hexp : Real.exp (-centralBound N/2) = (N : ℝ)^(-1/20 : ℝ) := by
    convert exp_logScale_mul hN (-1/20) using 1
    congr 1
    dsimp [centralBound]
    ring
  have hevent : probability (fixedCountPMF cuts) (fun ω => ¬collisionEvent w ω) =
      probability (fixedCountPMF cuts) (fun ω => wordCount w ω < 2) := by
    apply probability_congr
    intro ω
    simp only [collisionEvent, not_le]
  rw [hevent]
  exact htail.trans (by rw [← hexp]; linarith)

/-- Both nonrare regimes, including arbitrarily large means, under the actual law. -/
theorem nonrare_pair_relative (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ k K : ℕ, (K : ℝ) ≤ C*logScale N →
      ∀ (cuts : Cuts k N K) (w v : Word k K), w ≠ v →
      (∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ)) →
      (∀ j, c*N ≤ (cuts.count j (v.get j) : ℝ)) →
      tau N < (N : ℝ)*wordMass cuts w → tau N < (N : ℝ)*wordMass cuts v →
      |probability (fixedCountPMF cuts) (fun ω => collisionEvent w ω ∧ collisionEvent v ω) -
        probability (fixedCountPMF cuts) (collisionEvent w)*probability (fixedCountPMF cuts) (collisionEvent v)| ≤
      128*tau N*probability (fixedCountPMF cuts) (collisionEvent w)*
        probability (fixedCountPMF cuts) (collisionEvent v) := by
  obtain ⟨N1,hN12,hM⟩ := uniform_marginal c C hc hC
  obtain ⟨A,hA,N2,hCentral⟩ := central_pair_absolute c C hc hC
  obtain ⟨N3,hB⟩ := eventual_nonrare_budgets A
  refine ⟨max N1 (max N2 N3), hN12.trans (le_max_left _ _), ?_⟩
  intro N hN k K hK cuts w v hwv hw hv hμ hν
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2 : N2 ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hN3 : N3 ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  obtain ⟨hNtwo,ht,hl,ha,he⟩ := hB N hN3
  have hNp : 0 < N := by omega
  have ht0 := (tau_pos hNp).le
  have hp := hM N hN1 k K hK cuts w hw
  have hq := hM N hN1 k K hK cuts v hv
  have hp0 := probability_nonneg (fixedCountPMF cuts) (collisionEvent w)
  have hq0 := probability_nonneg (fixedCountPMF cuts) (collisionEvent v)
  have hpL := nonrare_probability_lower cuts w hNp ht hμ hp
  have hqL := nonrare_probability_lower cuts v hNp ht hν hq
  have hlarge (u z : Word k K)
      (hu0 : 0 ≤ probability (fixedCountPMF cuts) (collisionEvent u))
      (huL : poissonBase*(tau N)^2/2 ≤ probability (fixedCountPMF cuts) (collisionEvent u))
      (hz : centralBound N < (N : ℝ)*wordMass cuts z) :
      |probability (fixedCountPMF cuts) (fun ω => collisionEvent u ω ∧ collisionEvent z ω) -
        probability (fixedCountPMF cuts) (collisionEvent u)*probability (fixedCountPMF cuts) (collisionEvent z)| ≤
      128*tau N*probability (fixedCountPMF cuts) (collisionEvent u)*probability (fixedCountPMF cuts) (collisionEvent z) := by
    have hcomp := large_word_complement cuts z hNp hz
    have hzhalf : (1/2 : ℝ) ≤ probability (fixedCountPMF cuts) (collisionEvent z) := by
      have hn := probability_not (fixedCountPMF cuts) (collisionEvent z)
      linarith
    have hprod := mul_le_mul huL hzhalf (by norm_num : (0 : ℝ) ≤ 1/2) hu0
    have hmul := mul_le_mul_of_nonneg_left hprod ht0
    have hcov := abs_probability_covariance_le_complement (fixedCountPMF cuts) (collisionEvent u) (collisionEvent z)
    have hprod0 : 0 ≤ tau N*probability (fixedCountPMF cuts) (collisionEvent u)*probability (fixedCountPMF cuts) (collisionEvent z) :=
      mul_nonneg (mul_nonneg ht0 hu0) (by linarith)
    nlinarith
  by_cases hvB : (N : ℝ)*wordMass cuts v ≤ centralBound N
  · by_cases hwB : (N : ℝ)*wordMass cuts w ≤ centralBound N
    · have hf := benchmark_lower_at_tau ht0 (by linarith) hμ
      have hg := benchmark_lower_at_tau ht0 (by linarith) hν
      have hbase0 : 0 ≤ poissonBase*(tau N)^2 := mul_nonneg poissonBase_pos.le (sq_nonneg _)
      have hf0 : 0 ≤ poissonCollision ((N : ℝ)*wordMass cuts w) := hbase0.trans hf
      have hg0 : 0 ≤ poissonCollision ((N : ℝ)*wordMass cuts v) := hbase0.trans hg
      have hfg := mul_le_mul hf hg hbase0 hf0
      have hfgτ := mul_le_mul_of_nonneg_left hfg ht0
      have hcentral := hCentral N hN2 k K hK cuts w v hwv hw hv hwB hvB
      have hj : |probability (fixedCountPMF cuts) (fun ω => collisionEvent w ω ∧ collisionEvent v ω) -
          poissonCollision ((N : ℝ)*wordMass cuts w)*poissonCollision ((N : ℝ)*wordMass cuts v)| ≤
          tau N*poissonCollision ((N : ℝ)*wordMass cuts w)*poissonCollision ((N : ℝ)*wordMass cuts v) := by
        nlinarith
      have hrel := pair_relative_of_benchmark hf0 hg0 (by positivity : 0 ≤ 8*tau N)
        (by linarith : 8*tau N ≤ 1/2) ht0 hp hq hj
      have hprod0 := mul_nonneg (mul_nonneg ht0 hp0) hq0
      nlinarith
    · have hh := hlarge v w hq0 hqL (lt_of_not_ge hwB)
      have hevent : probability (fixedCountPMF cuts) (fun ω => collisionEvent v ω ∧ collisionEvent w ω) =
          probability (fixedCountPMF cuts) (fun ω => collisionEvent w ω ∧ collisionEvent v ω) := by
        apply probability_congr
        intro ω
        exact and_comm
      rw [hevent] at hh
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
  · exact hlarge w v hp0 hpL (lt_of_not_ge hvB)

end RiffleLowerV2.Occupancy
