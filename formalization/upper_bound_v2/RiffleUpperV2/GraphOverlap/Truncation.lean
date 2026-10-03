import RiffleUpperV2.GraphOverlap.Density
import RiffleUpperV2.GraphOverlap.FiniteProbability

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2.Factorial
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def truncatedDensity (P : PMF Ω) (A : Ω → Prop) (f : Ω → Γ → ℝ) (x : Γ) : ℝ :=
  RiffleLowerV2.expect P (fun ω => if A ω then f ω x else 0)

theorem truncatedDensity_mean (P : PMF Ω) (Q : PMF Γ) (A : Ω → Prop)
    (f : Ω → Γ → ℝ) (hn : ∀ ω, RiffleLowerV2.expect Q (f ω) = 1) :
    RiffleLowerV2.expect Q (truncatedDensity P A f) = RiffleLowerV2.probability P A := by
  unfold truncatedDensity
  rw [expect_comm]
  unfold RiffleLowerV2.probability
  congr 1
  funext ω
  by_cases ha : A ω <;> simp only [ha, ↓reduceIte, expect_const, hn]

theorem truncatedDensity_second (P : PMF Ω) (Q : PMF Γ) (A : Ω → Prop)
    (f : Ω → Γ → ℝ) :
    RiffleLowerV2.expect Q (fun x => truncatedDensity P A f x ^ 2) =
      RiffleLowerV2.expect P (fun ω => RiffleLowerV2.expect P (fun ω' =>
        if A ω ∧ A ω' then RiffleLowerV2.expect Q (fun x => f ω x * f ω' x) else 0)) := by
  have hs (x : Γ) : truncatedDensity P A f x ^ 2 =
      RiffleLowerV2.expect P (fun ω => RiffleLowerV2.expect P (fun ω' =>
        (if A ω then f ω x else 0) * (if A ω' then f ω' x else 0))) := by
    rw [pow_two]
    exact expect_product P P _ _
  simp_rw [hs]
  rw [expect_comm]
  congr 1
  funext ω
  rw [expect_comm]
  congr 1
  funext ω'
  by_cases ha : A ω <;> by_cases hb : A ω' <;>
    simp [ha, hb, expect_const]

/-- Exact finite Fubini identity; the same one-matrix event is used twice. -/
theorem truncatedVariance_eq (P : PMF Ω) (Q : PMF Γ) (A : Ω → Prop)
    (f : Ω → Γ → ℝ) (hn : ∀ ω, RiffleLowerV2.expect Q (f ω) = 1) :
    RiffleLowerV2.expect Q
      (fun x => (truncatedDensity P A f x - RiffleLowerV2.probability P A)^2) =
      RiffleLowerV2.expect P (fun ω => RiffleLowerV2.expect P (fun ω' =>
        if A ω ∧ A ω' then RiffleLowerV2.expect Q (fun x => f ω x*f ω' x)-1 else 0)) := by
  let a := RiffleLowerV2.probability P A
  have ha : a^2 = RiffleLowerV2.expect P (fun ω => RiffleLowerV2.expect P
      (fun ω' => if A ω ∧ A ω' then (1 : ℝ) else 0)) := by
    have h := expect_product P P (fun ω => if A ω then (1 : ℝ) else 0)
      (fun ω => if A ω then (1 : ℝ) else 0)
    change a*a = _ at h
    rw [pow_two]
    exact h.trans (by
      congr 1
      funext ω
      congr 1
      funext ω'
      split_ifs <;> simp_all)
  have hexp : (fun x => (truncatedDensity P A f x - a)^2) =
      (fun x => truncatedDensity P A f x ^ 2 -
        2*a*truncatedDensity P A f x + a^2) := by funext x; ring
  change RiffleLowerV2.expect Q (fun x => (truncatedDensity P A f x-a)^2) = _
  rw [hexp, expect_add, expect_sub, expect_const_mul, expect_const,
    truncatedDensity_mean P Q A f hn]
  change RiffleLowerV2.expect Q (fun x => truncatedDensity P A f x^2)-2*a*a+a^2 = _
  have halg (b : ℝ) : b - 2*a*a + a^2 = b - a^2 := by ring
  rw [halg, truncatedDensity_second, ha, ← expect_sub]
  congr 1
  funext ω
  rw [← expect_sub]
  congr 1
  funext ω'
  split_ifs <;> simp

theorem truncatedRadicand_nonneg (P : PMF Ω) (Q : PMF Γ) (A : Ω → Prop)
    (f : Ω → Γ → ℝ) (hn : ∀ ω, RiffleLowerV2.expect Q (f ω) = 1) :
    0 ≤ RiffleLowerV2.expect P (fun ω => RiffleLowerV2.expect P (fun ω' =>
      if A ω ∧ A ω' then RiffleLowerV2.expect Q (fun x => f ω x*f ω' x)-1 else 0)) := by
  rw [← truncatedVariance_eq P Q A f hn]
  exact expect_nonneg _ (fun _ => sq_nonneg _)

/-- Generic normalized-density form, with every premise discharged below for the shuffle. -/
theorem truncatedDensityTV (P : PMF Ω) (Q R : PMF Γ) (A : Ω → Prop)
    (f : Ω → Γ → ℝ) (hf : ∀ ω x, 0 ≤ f ω x)
    (hn : ∀ ω, RiffleLowerV2.expect Q (f ω) = 1)
    (hR : ∀ x, (R x).toReal = (Q x).toReal * RiffleLowerV2.expect P (fun ω => f ω x)) :
    RiffleLowerV2.tv R Q ≤
      Real.sqrt (RiffleLowerV2.expect P (fun ω => RiffleLowerV2.expect P (fun ω' =>
        if A ω ∧ A ω' then RiffleLowerV2.expect Q (fun x => f ω x*f ω' x)-1 else 0))) / 2 +
      RiffleLowerV2.probability P (fun ω => ¬ A ω) := by
  let a := RiffleLowerV2.probability P A
  let b := RiffleLowerV2.probability P (fun ω => ¬ A ω)
  let h := truncatedDensity P A f
  let r := truncatedDensity P (fun ω => ¬ A ω) f
  have hab : a + b = 1 := by dsimp [a, b]; rw [probability_compl]; ring
  have hb : 0 ≤ b := expect_nonneg P (fun ω => by dsimp; split_ifs <;> positivity)
  have hr (x : Γ) : 0 ≤ r x := expect_nonneg P (fun ω => by
    by_cases ha : A ω
    · simp [ha]
    · simpa [ha] using hf ω x)
  have hm (x : Γ) : RiffleLowerV2.expect P (fun ω => f ω x) = h x + r x := by
    dsimp [h, r, truncatedDensity]
    rw [← expect_add]
    congr 1
    funext ω
    split_ifs <;> simp_all
  have ht : RiffleLowerV2.tv R Q =
      RiffleLowerV2.expect Q (fun x => |h x + r x - 1|)/2 := by
    unfold RiffleLowerV2.tv RiffleLowerV2.expect
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [hR, hm]
    have heq : (Q x).toReal * (h x+r x) - (Q x).toReal =
        (Q x).toReal * (h x+r x-1) := by ring
    rw [heq, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have hpoint (x : Γ) : |h x+r x-1| ≤ |h x-a|+r x+b := by
    have heq : h x+r x-1 = (h x-a)+(r x-b) := by linarith
    rw [heq]
    have habs : |r x-b| ≤ r x+b := by
      apply abs_le.mpr
      constructor <;> linarith [hr x]
    exact (abs_add_le _ _).trans (by linarith)
  have hbound := expect_mono Q hpoint
  rw [expect_add, expect_add, truncatedDensity_mean P Q (fun ω => ¬ A ω) f hn,
    expect_const] at hbound
  have hcs := expect_abs_le_sqrt Q (fun x => h x-a)
  have hvar := truncatedVariance_eq P Q A f hn
  change RiffleLowerV2.expect Q (fun x => (h x-a)^2) = _ at hvar
  rw [hvar] at hcs
  rw [ht]
  change _ ≤ _ + b
  change _ ≤ _ + b + b at hbound
  linarith

theorem physical_density {k N K : ℕ} (cuts : Cuts k N K) (σ : Permutation N) :
    (physicalInverseLaw cuts σ).toReal = (uniformPermutation N σ).toReal *
      RiffleLowerV2.expect (fixedCountPMF cuts) (fun ω => density (shuffleEdges ω) σ) := by
  rw [← RiffleLowerV2.Model.expect_singleton, physical_graph_representation]
  unfold RiffleLowerV2.graphMixtureLaw
  rw [RiffleLowerV2.Model.expect_bind]
  simp_rw [RiffleLowerV2.Model.expect_singleton]
  change RiffleLowerV2.expect (fixedCountPMF cuts)
    (fun ω => (graphLaw (shuffleEdges ω) σ).toReal) = _
  simp_rw [graphLaw_density]
  exact expect_const_mul _ _ _

/-- The concrete chronological inverse law, with a single-matrix truncation event. -/
theorem truncatedTV {k N K : ℕ} (cuts : Cuts k N K) (S1 : Sample cuts → Prop) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      Real.sqrt (expect (fixedCountPMF cuts) (fun ω => expect (fixedCountPMF cuts) (fun ω' =>
        if S1 ω ∧ S1 ω' then overlap (shuffleEdges ω) (shuffleEdges ω') - 1 else 0))) / 2 +
      probability (fixedCountPMF cuts) (fun ω => ¬ S1 ω) :=
  truncatedDensityTV (fixedCountPMF cuts) (uniformPermutation N) (physicalInverseLaw cuts)
    S1 (fun ω => density (shuffleEdges ω))
    (fun ω σ => density_nonneg _ σ) (fun ω => density_normalized _) (physical_density cuts)

theorem shuffleTruncatedRadicand_nonneg {k N K : ℕ} (cuts : Cuts k N K)
    (S1 : Sample cuts → Prop) :
    0 ≤ expect (fixedCountPMF cuts) (fun ω => expect (fixedCountPMF cuts) (fun ω' =>
      if S1 ω ∧ S1 ω' then overlap (shuffleEdges ω) (shuffleEdges ω') - 1 else 0)) :=
  truncatedRadicand_nonneg (fixedCountPMF cuts) (uniformPermutation N) S1
    (fun ω => density (shuffleEdges ω)) (fun ω => density_normalized _)

end RiffleUpperV2.GraphOverlap
