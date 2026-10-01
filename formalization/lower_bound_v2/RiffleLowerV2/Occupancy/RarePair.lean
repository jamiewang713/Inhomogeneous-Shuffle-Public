import RiffleLowerV2.Occupancy.Forcing
import RiffleLowerV2.Occupancy.Marginal
import RiffleLowerV2.Occupancy.Conditional

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Topology
open Filter

namespace RiffleLowerV2.Occupancy
open TimeProfile

/-- The rare factorial sandwich remains valid after multiplying by any event. -/
theorem weighted_rare_sandwich {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (X : Ω → ℕ) (A : Ω → Prop) :
    expect P (fun ω => falling (X ω) 2 * (if A ω then 1 else 0)) / 2 -
        expect P (fun ω => falling (X ω) 3 * (if A ω then 1 else 0)) / 3 ≤
      probability P (fun ω => 2 ≤ X ω ∧ A ω) ∧
    probability P (fun ω => 2 ≤ X ω ∧ A ω) ≤
      expect P (fun ω => falling (X ω) 2 * (if A ω then 1 else 0)) / 2 := by
  have hlo := Factorial.expect_mono P (f := fun ω =>
    (falling (X ω) 2 / 2 - falling (X ω) 3 / 3) * (if A ω then 1 else 0))
    (g := fun ω => if 2 ≤ X ω ∧ A ω then 1 else 0) (by
      intro ω
      by_cases ha : A ω
      · simpa [ha] using (Factorial.rare_pointwise (X ω)).1
      · simp [ha])
  have hhi := Factorial.expect_mono P
    (f := fun ω => if 2 ≤ X ω ∧ A ω then 1 else 0)
    (g := fun ω => (falling (X ω) 2 * (if A ω then 1 else 0)) / 2) (by
      intro ω
      by_cases ha : A ω
      · simpa [ha] using (Factorial.rare_pointwise (X ω)).2
      · simp [ha])
  have heq : (fun ω => (falling (X ω) 2 / 2 - falling (X ω) 3 / 3) *
      (if A ω then (1 : ℝ) else 0)) =
      (fun ω => (falling (X ω) 2 * (if A ω then 1 else 0)) / 2 -
        (falling (X ω) 3 * (if A ω then 1 else 0)) / 3) := by
    funext ω
    ring
  rw [heq, Factorial.expect_sub, Factorial.expect_div, Factorial.expect_div] at hlo
  rw [Factorial.expect_div] at hhi
  have hind : expect P (fun ω => if 2 ≤ X ω ∧ A ω then 1 else 0) =
      probability P (fun ω => 2 ≤ X ω ∧ A ω) := by
    unfold probability
    congr 1
    funext ω
    by_cases h : 2 ≤ X ω ∧ A ω <;> simp [h]
  rw [hind] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- A factorial comparison and a forcing stability estimate combine multiplicatively. -/
theorem weighted_moment_relative {E F M q L τ : ℝ}
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hE : |E-M| ≤ τ*M) (hF : |F-E*q| ≤ L*τ*E*q) :
    |F-M*q| ≤ (2*L+1)*τ*M*q := by
  have hEu : E ≤ 2*M := by
    have hh := (abs_le.mp hE).2
    have htM := mul_le_mul_of_nonneg_right hτ1 hM
    linarith
  have hEu' := mul_le_mul_of_nonneg_left hEu (mul_nonneg hL hτ)
  have hEu'' := mul_le_mul_of_nonneg_right hEu' hq
  have heq := mul_le_mul_of_nonneg_right hE hq
  have htri : |F-M*q| ≤ |F-E*q| + |E-M| * q := by
    calc
      _ = |(F-E*q)+(E-M)*q| := by congr 1; ring
      _ ≤ _ := by
        simpa only [abs_mul, abs_of_nonneg hq] using abs_add_le (F-E*q) ((E-M)*q)
  nlinarith

/-- Every numerical condition used in the rare pair proof has a uniform threshold. -/
theorem eventual_rare_pair_budgets (c C D H : ℝ) (hc : 0 < c) (hH : 0 < H) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      3 ≤ N ∧ 0 ≤ logScale N ∧ tau N ≤ 1/16 ∧ H*tau N ≤ 1/2 ∧
      9*D*(C*logScale N+1)/N ≤ tau N ∧
      (3 : ℝ) ≤ c*N ∧ (3 : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) := by
  obtain ⟨N1,hM⟩ := eventual_marginal_budgets D C 0
  have ht := eventually_negative_rpow_le (by norm_num : (-1/100 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1/16)
  have htH := eventually_negative_rpow_le (by norm_num : (-1/100 : ℝ) < 0)
    (show (0 : ℝ) < 1/(2*H) by positivity)
  have hpile : ∀ᶠ N : ℕ in atTop, (3 : ℝ) ≤ c*N := by
    filter_upwards [eventually_ge_atTop ⌈3/c⌉₊] with N hN
    have hle : 3/c ≤ (N : ℝ) := (Nat.le_ceil (3/c)).trans (by exact_mod_cast hN)
    have hh := (div_le_iff₀ hc).mp hle
    nlinarith
  obtain ⟨N2,hN2⟩ := eventually_atTop.mp
    ((eventually_ge_atTop 3).and (ht.and (htH.and hpile)))
  refine ⟨max N1 N2, ?_⟩
  intro N hN
  obtain ⟨hNtwo,hlog,_,hRare,_,_,hOrder⟩ := hM N ((le_max_left _ _).trans hN)
  obtain ⟨hNthree,htN,htHN,hpileN⟩ := hN2 N ((le_max_right _ _).trans hN)
  have hHτ : H*tau N ≤ 1/2 := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < 2*H by positivity)).mp htHN
    change tau N * (2*H) ≤ 1 at hh
    nlinarith
  exact ⟨hNthree, by linarith, htN, hHτ, hRare, hpileN, hOrder⟩

/-- A rare category has a uniform relative pair estimate against every other word,
including words with arbitrarily small or large means. -/
theorem rare_pair_relative_uniform (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N ≥ N0, ∀ k K : ℕ, (K : ℝ) ≤ C*logScale N →
      ∀ (cuts : Cuts k N K) (w v : Word k K), w ≠ v →
        (∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ)) →
        (∀ j, c*N ≤ (cuts.count j (v.get j) : ℝ)) →
        (N : ℝ)*wordMass cuts w ≤ tau N →
      |probability (fixedCountPMF cuts) (fun ω => collisionEvent w ω ∧ collisionEvent v ω) -
        probability (fixedCountPMF cuts) (collisionEvent w)*probability (fixedCountPMF cuts) (collisionEvent v)| ≤
      D*tau N*probability (fixedCountPMF cuts) (collisionEvent w)*
        probability (fixedCountPMF cuts) (collisionEvent v) := by
  obtain ⟨D,hD,N1,hMoment⟩ := original_one_factorial_inputs c C hc hC
  obtain ⟨N2,hN2two,hMarginal⟩ := uniform_marginal c C hc hC
  obtain ⟨J,hJ,N3,hN3three,hN3two,hConditional⟩ := conditionalCollisionStability c C hc hC 3
  let L : ℝ := 2*(J+8)
  let H : ℝ := 2*L+1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hHone : 1 ≤ H := by dsimp [H]; linarith
  obtain ⟨N4,hBudget⟩ := eventual_rare_pair_budgets c C D H hc hH
  let N0 := N1+N2+N3+N4+3
  refine ⟨16*H, by positivity, N0, by dsimp [N0]; omega, ?_⟩
  intro N hN k K hK cuts w v hwv hw hv hrare
  have hN1 : N1 ≤ N := by dsimp [N0] at hN; omega
  have hN2 : N2 ≤ N := by dsimp [N0] at hN; omega
  have hN3 : N3 ≤ N := by dsimp [N0] at hN; omega
  have hN4 : N4 ≤ N := by dsimp [N0] at hN; omega
  obtain ⟨hNthree,hLog,hτsmall,hHτ,hRare,hPile,hOrder⟩ := hBudget N hN4
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hτ : 0 ≤ tau N := (tau_pos hNp).le
  let P := fixedCountPMF cuts
  let μ : ℝ := (N : ℝ)*wordMass cuts w
  let p : ℝ := probability P (collisionEvent w)
  let q : ℝ := probability P (collisionEvent v)
  let E : ℕ → ℝ := fun b => expect P (fun ω => falling (wordCount w ω) b)
  let F : ℕ → ℝ := fun b => expect P
    (fun ω => falling (wordCount w ω) b * (if collisionEvent v ω then 1 else 0))
  have hμ : 0 < μ := wordMean_pos cuts w hc hNp hw
  have hq : 0 ≤ q := probability_nonneg P (collisionEvent v)
  have hmom (b : ℕ) (hb : b ≤ 3) : |E b - μ^b| ≤ tau N*μ^b := by
    have hbR : (b : ℝ) ≤ 3 := by exact_mod_cast hb
    have hh := hMoment N hN1 k K hK cuts w hw b (hbR.trans hOrder)
    have hcoef : D*(K+1)*(b : ℝ)^2/N ≤ 9*D*(C*logScale N+1)/N := by
      apply div_le_div_of_nonneg_right _ hNr.le
      have hk : (K : ℝ)+1 ≤ C*logScale N+1 := by linarith
      have hkb := mul_le_mul_of_nonneg_left hk hD.le
      have hbb : (b : ℝ)^2 ≤ 9 := by nlinarith [Nat.cast_nonneg (α := ℝ) b]
      have hmul := mul_le_mul_of_nonneg_left hbb (show 0 ≤ D*((K : ℝ)+1) by positivity)
      nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right (hcoef.trans hRare) (pow_nonneg hμ.le _))
  have hforcing (b : ℕ) (hb : b ≤ 3) (e : Fin b ↪ Fin N) :
      0 < probability P (prescriptionEvent (sameWordPrescription w e)) := by
    apply sameWord_forcing_pos cuts w e (by omega)
    intro j
    have hbR : (b : ℝ) ≤ 3 := by exact_mod_cast hb
    have hh := hbR.trans (hPile.trans (hw j))
    exact_mod_cast hh
  have hqMarginal := hMarginal N hN2 k K hK cuts v hv
  have hf : 0 ≤ poissonCollision ((N : ℝ)*wordMass cuts v) :=
    (poissonCollision_pos (wordMean_pos cuts v hc hNp hv)).le
  have hfq : poissonCollision ((N : ℝ)*wordMass cuts v) ≤ 2*q := by
    have hlo := (abs_le.mp hqMarginal).1
    have ht := mul_le_mul_of_nonneg_right hτsmall hf
    change -(8*tau N*poissonCollision ((N : ℝ)*wordMass cuts v)) ≤
      q-poissonCollision ((N : ℝ)*wordMass cuts v) at hlo
    nlinarith
  have hcond (b : ℕ) (hb : b ≤ 3) (e : Fin b ↪ Fin N) :
      |conditionalProbability P (collisionEvent v) (prescriptionEvent (sameWordPrescription w e)) - q| ≤
        (L*tau N)*q := by
    have hh := hConditional N hN3 k K b hb hK cuts (sameWordPrescription w e) v
      e.injective (hforcing b hb e) hv
    rw [sameWord_prescribed_other_count w v e hwv] at hh
    simp only [Nat.sub_zero] at hh
    change |conditionalProbability P (collisionEvent v) (prescriptionEvent (sameWordPrescription w e)) -
      poissonCollision ((N : ℝ)*wordMass cuts v)| ≤
      J*tau N*poissonCollision ((N : ℝ)*wordMass cuts v) at hh
    have htri := abs_sub_le
      (conditionalProbability P (collisionEvent v) (prescriptionEvent (sameWordPrescription w e)))
      (poissonCollision ((N : ℝ)*wordMass cuts v)) q
    rw [abs_sub_comm (poissonCollision ((N : ℝ)*wordMass cuts v)) q] at htri
    have hbound := mul_le_mul_of_nonneg_left hfq
      (show 0 ≤ (J+8)*tau N by positivity)
    dsimp [L]
    change |q-poissonCollision ((N : ℝ)*wordMass cuts v)| ≤
      8*tau N*poissonCollision ((N : ℝ)*wordMass cuts v) at hqMarginal
    nlinarith
  have hweighted (b : ℕ) (hb : b ≤ 3) : |F b - μ^b*q| ≤ (H*tau N)*μ^b*q := by
    have hforce := forcing_weighted_relative_error cuts w (collisionEvent v) (L*tau N)
      (hforcing b hb) (hcond b hb)
    change |F b-E b*q| ≤ L*tau N*E b*q at hforce
    have hh := weighted_moment_relative (pow_nonneg hμ.le b) hq hL hτ
      (by linarith : tau N ≤ 1) (hmom b hb) hforce
    simpa only [H, mul_assoc] using hh
  have hs := Factorial.rareSandwich (Sample cuts) P (wordCount w)
  have hj := weighted_rare_sandwich P (wordCount w) (collisionEvent v)
  have hE2 := hmom 2 (by norm_num)
  have hE3 := hmom 3 (by norm_num)
  have hpLower : μ^2/4 ≤ p :=
    rare_marginal_lower hμ.le hrare (by linarith : tau N ≤ 1/4) hτ le_rfl hE2 hE3 hs.1 hs.2
  have hτH : tau N ≤ H*tau N := by nlinarith
  have hE2H := hE2.trans (mul_le_mul_of_nonneg_right hτH (sq_nonneg μ))
  have hE3H := hE3.trans (mul_le_mul_of_nonneg_right hτH (pow_nonneg hμ.le 3))
  have hh := rare_pair_relative hμ (hrare.trans hτH) hHτ
    (mul_nonneg hH.le hτ) le_rfl hq hE2H hE3H
    (hweighted 2 (by norm_num)) (hweighted 3 (by norm_num)) hs.1 hs.2 hj.1 hj.2 hpLower
  have hcw : (collisionEvent w : Sample cuts → Prop) = (fun ω => 2 ≤ wordCount w ω) := rfl
  have hcv : (collisionEvent v : Sample cuts → Prop) = (fun ω => 2 ≤ wordCount v ω) := rfl
  simpa only [P, p, q, hcw, hcv, mul_assoc] using hh

end RiffleLowerV2.Occupancy
