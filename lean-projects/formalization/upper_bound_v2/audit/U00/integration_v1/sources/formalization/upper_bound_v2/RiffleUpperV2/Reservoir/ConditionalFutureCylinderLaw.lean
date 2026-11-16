import RiffleUpperV2.Reservoir.LabelAveraging

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

def directionalWord {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) : Word k (L+1) :=
  sortedWord ω (pilePosition cuts p d j)

def strictlyFuture {k d : ℕ} (direction : Direction) (s w : Word k d) : Prop :=
  match direction with
  | .forward => s<w
  | .backward => w<s

theorem conditionalProbability_indicator {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E H : Ω → Prop) : conditionalProbability P E H=
      conditionalExpect P (fun ω => if E ω then (1:ℝ) else 0) H := by
  unfold conditionalProbability conditionalExpect RiffleLowerV2.conditionalProbability RiffleLowerV2.conditionalExpect
  congr 1
  unfold RiffleLowerV2.probability RiffleLowerV2.expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω <;> by_cases hh : H ω <;> simp only [he,hh,if_true,if_false,and_true,and_false,mul_zero,mul_one]

/-- Actual conditional graph law on every realized family-information atom.
The spatial direction never reverses the chronological tail columns. -/
theorem conditionalFutureCylinderLaw {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p))
    (x : I → Prefix k (L+1)) (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList →
      strictlyFuture d (directionalWord cuts p d ω₀ j) w) (E : Finset ℤ → Prop) :
    conditionalProbability (fixedCountPMF cuts) (fun ω => E (absoluteBlockGraph (x a) ω))
      (fun ω => futureFamilyView cuts p d (j.val+1) (directionalWord cuts p d ω₀ j) x ω=
        futureFamilyView cuts p d (j.val+1) (directionalWord cuts p d ω₀ j) x ω₀)=
    probability (fixedCountPMF (inducedCuts cuts (cylinderRows (x a) ω₀) (x a) ω₀))
      (fun σ => E ((shuffleEdges σ).image (fun e => (lowerRank (x a) ω₀:ℤ)+e.val))) := by
  have he : conditionalExpect (fixedCountPMF cuts)
      (fun ω => if E (absoluteBlockGraph (x a) ω) then (1:ℝ) else 0)
      (fun ω => futureFamilyView cuts p d (j.val+1) (directionalWord cuts p d ω₀ j) x ω=
        futureFamilyView cuts p d (j.val+1) (directionalWord cuts p d ω₀ j) x ω₀)=
      inducedGraphExpectation cuts (x a) ω₀ (fun G => if E G then 1 else 0) := by
    cases d with
    | forward => exact futureCylinderGraphExpect_forward cuts p ω₀ j x hsep a hfuture (fun G => if E G then (1:ℝ) else 0)
    | backward => exact futureCylinderGraphExpect_backward cuts p ω₀ j x hsep a hfuture (fun G => if E G then (1:ℝ) else 0)
  rw [conditionalProbability_indicator]
  exact he

/-- Erasing the labeled sets preserves the identical conditional graph law. -/
theorem conditionalFutureCylinderLaw_unlabeled {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p))
    (x : I → Prefix k (L+1)) (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList →
      strictlyFuture d (directionalWord cuts p d ω₀ j) w) (E : Finset ℤ → Prop) :
    conditionalProbability (fixedCountPMF cuts) (fun ω => E (absoluteBlockGraph (x a) ω))
      (fun ω => unlabeledFamilyView cuts p d (j.val+1) (directionalWord cuts p d ω₀ j) x ω=
        unlabeledFamilyView cuts p d (j.val+1) (directionalWord cuts p d ω₀ j) x ω₀)=
    probability (fixedCountPMF (inducedCuts cuts (cylinderRows (x a) ω₀) (x a) ω₀))
      (fun σ => E ((shuffleEdges σ).image (fun e => (lowerRank (x a) ω₀:ℤ)+e.val))) := by
  have he : conditionalExpect (fixedCountPMF cuts)
      (fun ω => if E (absoluteBlockGraph (x a) ω) then (1:ℝ) else 0)
      (fun ω => unlabeledFamilyView cuts p d (j.val+1) (directionalWord cuts p d ω₀ j) x ω=
        unlabeledFamilyView cuts p d (j.val+1) (directionalWord cuts p d ω₀ j) x ω₀)=
      inducedGraphExpectation cuts (x a) ω₀ (fun G => if E G then 1 else 0) := by
    cases d with
    | forward => exact unlabeledCylinderGraphExpect_forward cuts p ω₀ j x hsep a hfuture (fun G => if E G then (1:ℝ) else 0)
    | backward => exact unlabeledCylinderGraphExpect_backward cuts p ω₀ j x hsep a hfuture (fun G => if E G then (1:ℝ) else 0)
  rw [conditionalProbability_indicator]
  exact he

end RiffleUpperV2.Reservoir
