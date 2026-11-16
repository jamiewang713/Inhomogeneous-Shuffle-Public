import EdgeLocalization.Density
import Mathlib.Data.List.Lex

/-! Frozen ambient-relative definitions R.D01–03. -/

noncomputable section

namespace EdgeLocalization

def relativeInternalEdges (N : ℕ) (rows : ℕ → List ℕ)
    (xList : List ℕ) (s : ℕ) : Finset ℕ :=
  (Finset.range (N - 1)).filter (fun i => i + s ∈ internalEdges N rows xList)

def relativeEdgeDensity {Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω) (N : ℕ)
    (R : Ω → ℕ → List ℕ) (xList : List ℕ) (shift : Ω → ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N - 1),
    (w.probability (fun ω => i ∈ relativeInternalEdges N (R ω) xList (shift ω))) ^ 2

def ambientLeft (N : ℕ) (rows : ℕ → List ℕ) (wList : List ℕ) : ℕ :=
  ((Finset.range N).filter (fun i => rows i < wList)).card

end EdgeLocalization
