import Shuffle.FixedColumns
import Shuffle.FiniteMixture

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Shuffle

variable {Θ ι V : Type*} [Fintype Θ] [Fintype ι] [Fintype V] {k : ℕ}

/-- The common raw outcome space permits arbitrary mixtures of feasible arrays. -/
def rawMatrixLaw (h : ι → Histogram V k) : FiniteLaw (ι → V → Fin k) :=
  FiniteLaw.product (fun i => (columnLaw (h i)).map Subtype.val)

theorem rawMatrixLaw_rectangle (h : ι → Histogram V k)
    (E : ι → (V → Fin k) → Prop) :
    (rawMatrixLaw h).prob (fun x => ∀ i, E i (x i)) =
      ∏ i, (columnLaw (h i)).prob (fun f => E i f.val) := by
  rw [rawMatrixLaw, FiniteLaw.product_prob_rectangle]
  simp only [FiniteLaw.map_prob]

/-- D6 samples the complete histogram array with an arbitrary finite law. -/
def randomMatrixLaw (p : FiniteLaw Θ) (h : Θ → ι → Histogram V k) :
    FiniteLaw (ι → V → Fin k) :=
  p.mixture (fun θ => rawMatrixLaw (h θ))

/-- Keep the pile array available for conditioning, rather than discarding it. -/
def histogramMatrixJoint (p : FiniteLaw Θ) (h : Θ → ι → Histogram V k) :
    FiniteLaw (Θ × (ι → V → Fin k)) :=
  p.joint (fun θ => rawMatrixLaw (h θ))

theorem randomMatrixLaw_prob (p : FiniteLaw Θ) (h : Θ → ι → Histogram V k)
    (E : (ι → V → Fin k) → Prop) :
    (randomMatrixLaw p h).prob E = ∑ θ, p.mass θ * (rawMatrixLaw (h θ)).prob E :=
  FiniteLaw.mixture_prob p _ E

theorem histogramMatrixJoint_marginal (p : FiniteLaw Θ)
    (h : Θ → ι → Histogram V k) :
    (histogramMatrixJoint p h).map Prod.snd = randomMatrixLaw p h :=
  FiniteLaw.joint_second_map p _

/-- Given a positive complete-pile-array atom, the matrix has exactly the
independent fixed-column law. No independence of pile sizes is required. -/
theorem conditional_randomMatrixLaw (p : FiniteLaw Θ)
    (h : Θ → ι → Histogram V k) (θ : Θ) (hθ : 0 < p.mass θ) :
    ((histogramMatrixJoint p h).condition (fun x => x.1 = θ) (by
      change 0 < (p.joint (fun a => rawMatrixLaw (h a))).prob _
      rw [FiniteLaw.joint_first_prob]
      exact hθ)).map Prod.snd =
      rawMatrixLaw (h θ) :=
  FiniteLaw.joint_condition_second_map p (fun a => rawMatrixLaw (h a)) θ hθ

theorem conditional_randomMatrix_rectangle (p : FiniteLaw Θ)
    (h : Θ → ι → Histogram V k) (θ : Θ) (hθ : 0 < p.mass θ)
    (E : ι → (V → Fin k) → Prop) :
    (histogramMatrixJoint p h).conditionalProb (fun x => x.1 = θ)
        (fun x => ∀ i, E i (x.2 i)) =
      ∏ i, (columnLaw (h θ i)).prob (fun f => E i f.val) := by
  change (p.joint (fun a => rawMatrixLaw (h a))).conditionalProb _ _ = _
  rw [FiniteLaw.joint_conditional_second p (fun a => rawMatrixLaw (h a)) θ hθ
    (fun x : ι → V → Fin k => ∀ i, E i (x i))]
  exact rawMatrixLaw_rectangle (h θ) E

end Shuffle
