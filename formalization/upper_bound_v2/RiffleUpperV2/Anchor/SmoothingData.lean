import RiffleUpperV2.Anchor.JoinMaximizers

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile RiffleLowerV2.Thinning.Compat

/-- Exact reveal data, constructed below from the actual fixed-count law.
This structure is an output; no public smoothing theorem assumes it. -/
structure EndpointReveal {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) where
  History : Type
  finiteHistory : Fintype History
  history : Sample cuts → History
  good : Sample cuts → Prop
  params : Sample cuts → HypergeomParams
  shift : Sample cuts → ℤ
  refines : Refines history (internalHistory R x)
  good_measurable : ∀ ω₀ ω, history ω = history ω₀ → (good ω ↔ good ω₀)
  shift_measurable : ∀ ω₀ ω, history ω = history ω₀ → shift ω = shift ω₀
  endpoint_law : ∀ ω₀ (f : ℤ → ℝ),
    conditionalExpect (fixedCountPMF cuts) (fun ω => f (lowerEndpoint c₀ R x ω))
      (fun ω => history ω = history ω₀) = expect (params ω₀).law.toPMF (fun q => f (shift ω₀ + q.val)) ∧
    conditionalExpect (fixedCountPMF cuts) (fun ω => f (upperEndpoint c₀ R x ω))
      (fun ω => history ω = history ω₀) = expect (params ω₀).law.toPMF
        (fun q => f (shift ω₀ + q.val + (prefixRows R x ω₀).card))

/-- The quantitative fields are proved from reserve and genuine crossings by
the constructor in Smoothing; they are never required as an external input. -/
structure EndpointSmoothingData {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (g w D : ℝ) extends EndpointReveal cuts c₀ R x where
  failure : probability (fixedCountPMF cuts) (fun ω => ¬ good ω) ≤
    3 * Real.exp (-RiffleLowerV2.chernoffConstant*g*w)
  variance : ∀ ω, good ω → g*w/(16*D) ≤ (params ω).varianceFormula

/-- Concrete equal-set reveal and both endpoint laws. -/
def exactEqualReveal {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) : EndpointReveal cuts c₀ R x where
  History := (Fin d → Option (Fin n → Fin k)) × Finset (Fin n)
  finiteHistory := inferInstance
  history := equalRevealHistory (prefixColumn x j) (x.2.get j)
  good := equalGood cuts R x j
  params := equalEndpointParams R x j
  shift := equalShift c₀ R x j
  refines := equalReveal_refines_internal R x j
  good_measurable := fun ω₀ ω hh => equalGood_measurable cuts R x j
    ((equalRevealHistory_eq_iff _ _ ω₀ ω).mp hh)
  shift_measurable := fun ω₀ ω hh => (equalShift_eq_of_equalReveal c₀ R x j
    ((equalRevealHistory_eq_iff _ _ ω₀ ω).mp hh)).1
  endpoint_law := by
    intro ω₀ f
    have hF : (fun ω => equalRevealHistory (prefixColumn x j) (x.2.get j) ω =
        equalRevealHistory (prefixColumn x j) (x.2.get j) ω₀) =
        equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ := by
      funext ω
      exact propext (equalRevealHistory_eq_iff _ _ ω₀ ω)
    rw [hF]
    exact endpointShiftHypergeometric_equal cuts c₀ R x j ω₀ f

/-- Concrete unequal reveal; its B0 event is fixed by the other columns. -/
def exactUnequalReveal {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val) : EndpointReveal cuts c₀ R x where
  History := (Fin d → Option (Fin n → Fin k)) × (Fin n → Option (Fin k))
  finiteHistory := inferInstance
  history := unequalRevealHistory s R x j
  good := unequalGood cuts s R x i j
  params := unequalEndpointParams s R x j
  shift := unequalShift s c₀ R x j
  refines := unequalReveal_refines_internal s R x j
  good_measurable := fun ω₀ ω hh => unequalGood_measurable cuts s R x i j
    ((unequalRevealHistory_eq_iff s R x j ω₀ ω).mp hh)
  shift_measurable := fun ω₀ ω hh => (unequalShift_eq_of_unequalReveal s c₀ R x j
    ((unequalRevealHistory_eq_iff s R x j ω₀ ω).mp hh)).1
  endpoint_law := by
    intro ω₀ f
    have hF : (fun ω => unequalRevealHistory s R x j ω = unequalRevealHistory s R x j ω₀) =
        unequalRevealFiber s R x j ω₀ := by
      funext ω
      exact propext (unequalRevealHistory_eq_iff s R x j ω₀ ω)
    rw [hF]
    exact endpointShiftHypergeometric_unequal cuts s c₀ R x j ω₀ f

end RiffleUpperV2.Anchor
