import RiffleProfiles.MatrixLaw
import RiffleProfiles.BoundaryTruncation
import RiffleProfiles.ExceptionalTruncation

/-! Frozen T09: finite truncation bounds under the actual matrix sampling law. -/

noncomputable section
open scoped BigOperators

namespace RiffleProfiles

attribute [local instance] Classical.propDecidable

theorem model_discardedBoundary_expected_rows_le {D : Riffle.Model}
    (A : Riffle.Setup D) (s : Riffle.Side) :
    (Shuffle.fixedMatrixLaw (modelHistogram D)).expect
      (fun matrix => ((Finset.univ.filter (fun r : Fin D.N =>
        Riffle.fullList (modelRowWord D matrix r) ∈ discardedBoundary A s)).card : ℝ)) ≤
      (D.N : ℝ) * tailWeight D.K (Nat.floor (boundaryThreshold A) + 1)
        ((D.k : ℝ) * A.chi) := by
  rw [model_expected_row_count D (discardedBoundary A s)]
  exact discardedBoundary_expectedCount_le A s

theorem model_discardedBoundary_union_expected_rows_le {D : Riffle.Model}
    (A : Riffle.Setup D) :
    (Shuffle.fixedMatrixLaw (modelHistogram D)).expect
      (fun matrix => ((Finset.univ.filter (fun r : Fin D.N =>
        Riffle.fullList (modelRowWord D matrix r) ∈
          discardedBoundary A .left ∪ discardedBoundary A .right)).card : ℝ)) ≤
      2 * ((D.N : ℝ) * tailWeight D.K (Nat.floor (boundaryThreshold A) + 1)
        ((D.k : ℝ) * A.chi)) := by
  simpa only [Set.mem_union] using
    ((model_expected_row_count D
      (discardedBoundary A .left ∪ discardedBoundary A .right)).le.trans
      (discardedBoundary_union_expectedCount_le A))

private theorem model_expected_row_event (D : Riffle.Model)
    (E : Riffle.FullIndex D → Prop) :
    (Shuffle.fixedMatrixLaw (modelHistogram D)).expect
      (fun matrix => ((Finset.univ.filter (fun r : Fin D.N =>
        E (modelRowWord D matrix r))).card : ℝ)) =
      (D.N : ℝ) * ∑ ω : Riffle.FullIndex D,
        if E ω then wordWeight (modelDigitProb D) ω else 0 := by
  let EL : Set Riffle.Word := Riffle.fullList '' {ω : Riffle.FullIndex D | E ω}
  have hEL (ω : Riffle.FullIndex D) : Riffle.fullList ω ∈ EL ↔ E ω := by
    constructor
    · rintro ⟨σ, hσ, hσω⟩
      exact Riffle.fullList_injective hσω ▸ hσ
    · intro hω
      exact ⟨ω, hω, rfl⟩
  have hid := model_expected_row_count D EL
  rw [model_expectedCount_eq_wordMass] at hid
  simpa only [hEL] using hid

theorem model_exceptionalPrefix_expected_rows_le (D : Riffle.Model)
    (P : TimeProfile.BorelPartition D.k) (χ C α : ℝ)
    (v M : Riffle.FullIndex D → ℕ) (hreg : P.IsRegular χ C)
    (hχ : 0 < χ) (hα : 0 ≤ α) :
    (Shuffle.fixedMatrixLaw (modelHistogram D)).expect
      (fun matrix => ((Finset.univ.filter (fun r : Fin D.N =>
        α < ((sourceExceptionalPositions (modelColumnProfile D) P χ v M
          (modelRowWord D matrix r)).card : ℝ) / TimeProfile.logScale D.N)).card : ℝ)) ≤
      (D.N : ℝ) * tailWeight D.K (Nat.floor (α * TimeProfile.logScale D.N) + 1)
        ((D.k : ℝ) * (3 * χ)) := by
  rw [model_expected_row_event D (fun ω =>
    α < ((sourceExceptionalPositions (modelColumnProfile D) P χ v M ω).card : ℝ) /
      TimeProfile.logScale D.N)]
  simpa only [modelColumnProfile_prob] using
    exceptionalPrefix_scaled_wordMass_le D.N (modelColumnProfile D) P χ C α v M
      hreg hχ (by have := D.one_lt_N; omega) hα

end RiffleProfiles
