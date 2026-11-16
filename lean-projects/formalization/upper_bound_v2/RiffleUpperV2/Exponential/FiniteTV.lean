import RiffleUpperV2.Exponential.Aggregation
import RiffleUpperV2.GraphOverlap.Truncation
import RiffleUpperV2.GraphOverlap.RunProduct

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exponential
open RiffleLowerV2.Thinning

/-- The graph-majorization form of the finite criterion. The physical inverse law and
single-matrix product truncation are exact. The explicit graph majorization premise is
consumed by the bounded-component specialization. -/
theorem finiteExplorationTV_of_majorization {k N K : ℕ} (cuts : Cuts k N K)
    (S1 : Sample cuts → Prop) (d : ℕ) (hd : 0 < d)
    (H : Fin d → Type*) [∀ a, Fintype (H a)]
    (h : ∀ a, ℕ → (Sample cuts × Sample cuts) → H a)
    (X : Fin d → ℕ → (Sample cuts × Sample cuts) → ℕ)
    (B : Fin d → ℕ → (Sample cuts × Sample cuts) → Prop) (m : Fin d → ℕ)
    (γ b : ℝ) (hγ : 0 ≤ γ) (hb : 1 ≤ b)
    (href : ∀ a, Refining (h a) (m a))
    (hunit : ∀ a ω, UnitIncrements (fun i => X a i ω) (m a))
    (hzero : ∀ a ω, X a 0 ω = 0)
    (had : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (X a i))
    (hB : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (B a i))
    (htail : ∀ a i, i < m a → ∀ v, B a i v →
      0 < probability (independentPairLaw cuts) (fun ω => h a i ω = h a i v) →
      conditionalExpect (independentPairLaw cuts)
        (fun ω => (X a (m a) ω - X a i ω : ℕ)) (fun ω => h a i ω = h a i v) ≤ γ)
    (hC : ∀ ω : Sample cuts × Sample cuts, S1 ω.1 ∧ S1 ω.2 →
      ∀ a, goodPrefix (B a) (m a) ω)
    (hcover : ∀ ω : Sample cuts × Sample cuts, S1 ω.1 ∧ S1 ω.2 →
      (shuffleEdges ω.1 ∩ shuffleEdges ω.2).card ≤ ∑ a, X a (m a) ω)
    (hmajor : ∀ ω ω' : Sample cuts, S1 ω → S1 ω' →
      GraphOverlap.overlap (shuffleEdges ω) (shuffleEdges ω') ≤
        b^((shuffleEdges ω ∩ shuffleEdges ω').card))
    (hqγ : (b^d - 1)*γ < 1) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      Real.sqrt ((b^d - 1)*γ / (1-(b^d - 1)*γ)) / 2 +
      probability (fixedCountPMF cuts) (fun ω => ¬ S1 ω) := by
  have he := finiteExplorationExcess (independentPairLaw cuts) d hd H h X B m γ b hγ hb
    href hunit hzero had hB htail (fun ω => S1 ω.1 ∧ S1 ω.2) hC
    (fun ω => (shuffleEdges ω.1 ∩ shuffleEdges ω.2).card) hcover hqγ
  have hmajor' : expect (fixedCountPMF cuts) (fun ω => expect (fixedCountPMF cuts) (fun ω' =>
      if S1 ω ∧ S1 ω' then GraphOverlap.overlap (shuffleEdges ω) (shuffleEdges ω')-1 else 0)) ≤
      expect (independentPairLaw cuts) (fun ω => if S1 ω.1 ∧ S1 ω.2 then
        b^((shuffleEdges ω.1 ∩ shuffleEdges ω.2).card)-1 else 0) := by
    have heq := independentPair_expect cuts (fun ω ω' =>
      if S1 ω ∧ S1 ω' then b^((shuffleEdges ω ∩ shuffleEdges ω').card)-1 else 0)
    simp only [ite_and] at heq ⊢
    rw [heq]
    apply expect_mono
    intro ω
    apply expect_mono
    intro ω'
    by_cases h1 : S1 ω
    · by_cases h2 : S1 ω'
      · simp only [h1, h2, if_true]
        exact sub_le_sub_right (hmajor ω ω' h1 h2) 1
      · simp only [h1, h2, if_true, if_false, le_refl]
    · simp only [h1, if_false, le_refl]
  have he' : expect (independentPairLaw cuts) (fun ω => if S1 ω.1 then
      if S1 ω.2 then b^((shuffleEdges ω.1 ∩ shuffleEdges ω.2).card)-1 else 0 else 0) ≤
      (b^d - 1)*γ / (1-(b^d - 1)*γ) := by
    convert he using 1
    congr 1
    funext ω
    by_cases h1 : S1 ω.1 <;> by_cases h2 : S1 ω.2 <;> simp [h1, h2]
  simp only [ite_and] at hmajor'
  have hrad := hmajor'.trans he' 
  apply (GraphOverlap.truncatedTV cuts S1).trans
  simp only [ite_and]
  have hs := Real.sqrt_le_sqrt hrad
  linarith

/-- The exact central-binomial component constant in the finite exploration criterion. -/
def componentConstant (B : ℕ) : ℝ := (B.choose (B/2) : ℝ)

theorem componentConstant_ge_one (B : ℕ) : 1 ≤ componentConstant B := by
  unfold componentConstant
  exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos (Nat.div_le_self B 2))

/-- Source finite d-exploration TV criterion. Every graph-majorization premise is
proved here from the actual component bound; exploration premises remain explicit
for the concrete empirical theorem to discharge. -/
theorem finiteExplorationTV {k N K : ℕ} (cuts : Cuts k N K)
    (S1 : Sample cuts → Prop) (bound : ℕ) (hbound : 2 ≤ bound)
    (hcomp : ∀ ω, S1 ω → GraphOverlap.BoundedComponents (shuffleEdges ω) bound)
    (d : ℕ) (hd : 0 < d) (H : Fin d → Type*) [∀ a, Fintype (H a)]
    (h : ∀ a, ℕ → (Sample cuts × Sample cuts) → H a)
    (X : Fin d → ℕ → (Sample cuts × Sample cuts) → ℕ)
    (B : Fin d → ℕ → (Sample cuts × Sample cuts) → Prop) (m : Fin d → ℕ)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (href : ∀ a, Refining (h a) (m a))
    (hunit : ∀ a ω, UnitIncrements (fun i => X a i ω) (m a))
    (hzero : ∀ a ω, X a 0 ω = 0)
    (had : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (X a i))
    (hB : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (B a i))
    (htail : ∀ a i, i < m a → ∀ v, B a i v →
      0 < probability (independentPairLaw cuts) (fun ω => h a i ω = h a i v) →
      conditionalExpect (independentPairLaw cuts)
        (fun ω => (X a (m a) ω - X a i ω : ℕ)) (fun ω => h a i ω = h a i v) ≤ γ)
    (hC : ∀ ω : Sample cuts × Sample cuts, S1 ω.1 ∧ S1 ω.2 →
      ∀ a, goodPrefix (B a) (m a) ω)
    (hcover : ∀ ω : Sample cuts × Sample cuts, S1 ω.1 ∧ S1 ω.2 →
      (shuffleEdges ω.1 ∩ shuffleEdges ω.2).card ≤ ∑ a, X a (m a) ω)
    (hqγ : ((componentConstant bound)^d - 1)*γ < 1) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      Real.sqrt (((componentConstant bound)^d - 1)*γ /
        (1-((componentConstant bound)^d - 1)*γ)) / 2 +
      probability (fixedCountPMF cuts) (fun ω => ¬ S1 ω) := by
  apply finiteExplorationTV_of_majorization cuts S1 d hd H h X B m γ
    (componentConstant bound) hγ (componentConstant_ge_one bound)
    href hunit hzero had hB htail hC hcover ?_ hqγ
  intro ω ω' _ hω'
  exact GraphOverlap.boundedComponentOverlap (shuffleEdges ω) (shuffleEdges ω') hbound (hcomp ω' hω')

end RiffleUpperV2.Exponential
