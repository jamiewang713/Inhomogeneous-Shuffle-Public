import RiffleUpperV2.FirstMoment.RetainedClasses
import RiffleUpperV2.Localization.DiscardedEdges
import RiffleUpperV2.Localization.FirstPileTransport

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric RiffleLowerV2.Thinning

/-- The finite function-word and vector-word APIs represent the same selected words. -/
def vectorWords {k d : ℕ} (W : Finset (Fin d → Fin k)) : Finset (Word k d) :=
  W.image List.Vector.ofFn

@[simp] theorem vector_ofFn_get {k d : ℕ} (w : Word k d) : List.Vector.ofFn w.get = w := by
  apply List.Vector.ext
  intro j
  simp

@[simp] theorem mem_vectorWords {k d : ℕ} (W : Finset (Fin d → Fin k)) (w : Word k d) :
    w ∈ vectorWords W ↔ w.get ∈ W := by
  classical
  constructor
  · rintro h
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
    have hget : (List.Vector.ofFn u).get = u := by funext j; simp
    simpa only [hget] using hu
  · intro h
    exact Finset.mem_image.mpr ⟨w.get,h,vector_ofFn_get w⟩

theorem rowsInWords_vectorWords {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (W : Finset (Fin d → Fin k)) (omega : Sample cuts) :
    Localization.rowsInWords R (vectorWords W) omega = FirstMoment.rowsInWords R W omega := by
  ext r
  have hrow : (rowWord omega r).get = sampleRow omega r := by
    funext j
    exact RiffleLowerV2.rowWord_get omega r j
  simp [Localization.rowsInWords,FirstMoment.rowsInWords,mem_vectorWords,hrow]

/-- The literal discarded-word edge marginals cost at most the already proved
actual discarded-row expectation. -/
theorem discardedEdges_total_le_discardedRows {k n d N : ℕ} (hk : 0 < k)
    (cuts : Cuts k n d) (hn : 0<n) (R : Finset (Fin n)) (C chi delta : ℝ)
    (hchiK : chi ≤ 1/(k : ℝ)) (c₀ : ℤ) (slots : Finset ℤ) :
    (∑ m ∈ slots, probability (fixedCountPMF cuts) (fun omega =>
      m ∈ edgesInWords c₀ R (vectorWords (discardedWords hk N cuts hn R C chi delta hchiK)) omega)) ≤
    expect (fixedCountPMF cuts) (fun omega =>
      ((FirstMoment.rowsInWords R (discardedWords hk N cuts hn R C chi delta hchiK) omega).card : ℝ)) := by
  have h := discardedEdges_total_le_rows cuts c₀ R
    (vectorWords (discardedWords hk N cuts hn R C chi delta hchiK)) slots
  simpa only [rowsInWords_vectorWords] using h

/-- Every actual pile edge is carried by one retained descriptor block, or by
an actual discarded full word. -/
theorem retainedGraphCover {k n d N : ℕ} (hk : 0 < k)
    (cuts : Cuts k n d) (hn : 0<n) (R : Fin k → Finset (Fin n)) (p : Fin k)
    (C chi delta : ℝ) (hchiK : chi ≤ 1/(k : ℝ)) (c₀ : ℤ)
    (omega : Sample cuts) (m : ℤ) (hm : m ∈ anchoredEdges c₀ (R p) (emptyPrefix k d) omega) :
    m ∈ edgesInWords c₀ (R p) (vectorWords (discardedWords hk N cuts hn (R p) C chi delta hchiK)) omega ∨
      ∃ t : RetainedAtPile hk N cuts hn R C chi delta hchiK,
        t.1=p ∧ m ∈ anchoredEdges c₀ (R p) t.2.1.2.2 omega := by
  obtain ⟨w,hw,_,hmw⟩ := (anchoredEdges_mem_legal_word cuts hn c₀ (R p) _ omega m).mp hm
  have hw' : Legal cuts (R p) (RiffleLowerV2.fullPrefix (List.Vector.ofFn w.get)) := by simpa using hw
  rcases fullWord_retained_or_discarded hk cuts hn R p C chi delta hchiK w.get hw' with hret | hdisc
  · obtain ⟨t,ht,hpre⟩ := hret
    exact Or.inr ⟨t,ht,(anchoredEdges_mem_legal_word cuts hn c₀ (R p) _ omega m).mpr
      ⟨w,hw,by simpa using hpre,hmw⟩⟩
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨w,(mem_vectorWords _ _).mpr hdisc,hmw⟩)

/-- The actual cover transported to the fixed-anchor future law. -/
theorem anchored_empty_probability_le {k n d N : ℕ} (hk : 0 < k)
    (cuts : Cuts k n d) (hn : 0<n) (R : Fin k → Finset (Fin n)) (p : Fin k)
    (C chi delta : ℝ) (hchiK : chi ≤ 1/(k : ℝ)) (c₀ : ℤ) (m : ℤ) :
    anchoredEdgeProbability cuts c₀ (R p) (emptyPrefix k d) m ≤
      probability (fixedCountPMF cuts) (fun omega =>
        m ∈ edgesInWords c₀ (R p) (vectorWords (discardedWords hk N cuts hn (R p) C chi delta hchiK)) omega) +
      ∑ t : RetainedAtPile hk N cuts hn R C chi delta hchiK,
        if t.1=p then anchoredEdgeProbability cuts c₀ (R p) t.2.1.2.2 m else 0 := by
  let bad := fun omega : Sample cuts =>
    m ∈ edgesInWords c₀ (R p) (vectorWords (discardedWords hk N cuts hn (R p) C chi delta hchiK)) omega
  let E := fun t : RetainedAtPile hk N cuts hn R C chi delta hchiK =>
    fun omega : Sample cuts => t.1=p ∧ m ∈ anchoredEdges c₀ (R p) t.2.1.2.2 omega
  have hcover : anchoredEdgeProbability cuts c₀ (R p) (emptyPrefix k d) m ≤
      probability (fixedCountPMF cuts) (fun omega => bad omega ∨ ∃ t, E t omega) :=
    probability_mono _ (fun omega hm => retainedGraphCover hk cuts hn R p C chi delta hchiK c₀ omega m hm)
  apply hcover.trans ((probability_union_le _ bad (fun omega => ∃ t, E t omega)).trans ?_)
  apply add_le_add le_rfl
  apply (probability_iUnion_le _ E).trans
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : t.1=p
  · simp only [ht,if_true]
    exact probability_mono _ (fun _ h => h.2)
  · simp [E,ht,probability,RiffleLowerV2.probability,RiffleLowerV2.expect]

end RiffleUpperV2.FirstMoment
