import RiffleUpperV2.Reservoir.FutureGraphLaw

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

/-- Erase only the labels; retain cardinality, absolute interval and induced counts. -/
def unlabeledCylinderRecord {k n d : ℕ} {cuts : Cuts k n d} (x : Prefix k d) (ω : Sample cuts) :=
  ((cylinderRows x ω).card,lowerRank x ω,upperRank x ω,
    fun j : Fin d => fun a : Fin k => ((cylinderRows x ω).filter fun r => sampleEntry ω r j=a).card)

def unlabeledFamilyView {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (i : ℕ) (s : Word k (L+1)) (x : I → Prefix k (L+1)) (ω : Sample cuts) :=
  (naturalHistory cuts p d i ω,(fun a => unlabeledCylinderRecord (x a) ω),wordCount ω s)

theorem futureFamilyView_refines_unlabeled {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) (s : Word k (L+1)) (x : I → Prefix k (L+1)) (ω σ : Sample cuts)
    (h : futureFamilyView cuts p d i s x ω=futureFamilyView cuts p d i s x σ) :
    unlabeledFamilyView cuts p d i s x ω=unlabeledFamilyView cuts p d i s x σ := by
  apply Prod.ext
  · have hh := congrArg Prod.fst h
    exact hh
  · apply Prod.ext
    · funext a
      have he := congrArg (fun z => z.2.1 a) h
      exact congrArg (fun z => (z.1.card,z.2)) he
    · exact congrArg (fun z => z.2.2) h

def shiftedGraphExpectation {k m d : ℕ} (cuts : Cuts k m d) (b : ℕ) (F : Finset ℤ → ℝ) : ℝ :=
  expect (fixedCountPMF cuts) (fun σ => F ((shuffleEdges σ).image (fun e => (b:ℤ)+e.val)))

theorem shiftedGraphExpectation_congr {k m m' d : ℕ} (cuts : Cuts k m d) (cuts' : Cuts k m' d)
    (hm : m=m') (hc : ∀ j a, cuts.count j a=cuts'.count j a) (b b' : ℕ) (hb : b=b')
    (F : Finset ℤ → ℝ) : shiftedGraphExpectation cuts b F=shiftedGraphExpectation cuts' b' F := by
  subst m'
  have he : cuts=cuts' := by
    cases cuts
    cases cuts'
    congr 1
    funext j a
    exact hc j a
  rw [he,hb]

/-- The graph-law value depends on the unlabeled record alone, including
empty cylinders and zero induced counts. -/
theorem inducedGraphExpectation_record_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (ω σ : Sample cuts) (h : unlabeledCylinderRecord x ω=unlabeledCylinderRecord x σ)
    (F : Finset ℤ → ℝ) : inducedGraphExpectation cuts x ω F=inducedGraphExpectation cuts x σ F := by
  have hm : (cylinderRows x ω).card=(cylinderRows x σ).card := congrArg Prod.fst h
  have hb : lowerRank x ω=lowerRank x σ := congrArg (fun z => z.2.1) h
  apply shiftedGraphExpectation_congr _ _ hm _ _ _ hb F
  intro j a
  exact congrArg (fun z => z.2.2.2 (suffixColumn x j) a) h

end RiffleUpperV2.Reservoir
