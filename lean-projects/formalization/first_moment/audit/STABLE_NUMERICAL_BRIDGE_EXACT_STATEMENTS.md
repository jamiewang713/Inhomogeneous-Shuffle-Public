# Exact binder and type audit: stable numerical bridge

Reviewed all four definitions and sixteen interfaces in `STABLE_NUMERICAL_BRIDGE_STATEMENTS.md` against the current project Lean declarations and the Lean 4.33 compatibility source metadata. This was a read-only source/binder audit; no new Lean declaration or implementation was created.

**Decision: approve the corrected candidate.** One elaboration clarification was applied before freeze: SN6 now spells `Riffle.fullList (D := D)`. SN7 already uses that explicit model argument. No mathematical premise, definition value, or conclusion changed. The corrected candidate has SHA-256 `05f5f072fb6d7061e85f4167dbe9566f6a3648a3729422f29b6e761a9ccb2138`.

## Namespace and import requirements

The implementation namespace remains `InhomogeneousShuffle.FirstMoment.Model`. Every proposed exported name is new in that namespace. The time-profile module paths begin `RiffleTimeProfile`, while their declaration namespace is **`TimeProfile`**; the signatures correctly use the latter. Stable declarations use `Riffle`.

The following existing module imports expose the main proof inputs:

```text
Riffle.SourceStable
Riffle.Pieces
RiffleTimeProfile.ExpectedMass
RiffleTimeProfile.SideMass
```

`Riffle.SourceStable` imports stopping/cost/word/boundary foundations, but **does not import `Riffle.Pieces`**. The latter must be imported explicitly for `pieceEvent_iff` and `cFAt_continuation`. `ExpectedMass` imports both `FixedCountMoments` and `FixedCountModel`, hence the finite sample, measure, row count, and exact moment declarations are present. `Riffle.Mass` is needed only if the implementation chooses the alternative direct product proof using `weight_eq_zero_of_not_legal`; it is not needed by the stated generic expected-count-to-integral route.

Use the ordinary `noncomputable section`, `open MeasureTheory`, and finite-sum notation setup where required. These are elaboration settings, not added assumptions or exported definitions. No custom instance is required in an interface: the fixed-count module already supplies finite, nonempty, measurable, singleton-measurable and probability-measure instances for its sample space.

The implicit model binder is `{D : Riffle.Model}` in SN2–SN5 and SN8–SN16; SN1, SN6 and SN7 have the explicit displayed `D`. No implicit natural parameter from the numerical package is left unconstrained. D4 has its own implicit `{k : ℕ}`.

## Four definitions

| Definition | Actual declaration check |
| --- | --- |
| `asCuts` | `TimeProfile.Cuts` takes parameters in order **`k N K`**. Its fields are exactly `count : Fin K → Fin k → ℕ` and **`sum_count`**, not `sum_counts`, with type `∀ j, ∑ l, count j l = N`. The source model field is instead **`D.sum_counts`**, with natural column `i`, a proof `i < D.K`, and a sum over `Finset.range D.k`. Thus the specified `count j l := D.n j.val l.val` and finite-index reindexing have the right types. |
| `asProfile` | `(asCuts D).profile` expects a proof `0 < D.N`, then `j : Fin D.K`. The candidate's `lt_trans Nat.zero_lt_one D.one_lt_N` has exactly that proof type. Its result is `TimeProfile.Simplex D.k`, giving the declared function type. |
| `legalVector` | `Riffle.Legal D x` unfolds to `x.length ≤ D.K ∧ ∀ i, i < x.length → digit x i < D.k ∧ 0 < D.n i (digit x i)`. Consequently `(hx.2 j.val hj).1` is the required alphabet bound. The zero suffix digit uses `0 < D.k`, derived from `D.two_le_k`; no suffix pile positivity is claimed. Proof irrelevance handles occurrences of different proofs of the same `Legal` proposition. |
| `sideProbability` | Both `TimeProfile.leftProbability` and `rightProbability` have type `Simplex k → Fin k → ℝ`. `Riffle.Side` has exactly constructors `.left` and `.right`. At each later application, the expected side-function type from `asProfile D` determines the implicit alphabet size as `D.k`. |

`Fin.sum_univ_eq_sum_range` is an existing trusted finite-index summation API; it is used in the current mathlib version as well. The four definitions need no source horizon, partition, ambient approximation, or stochastic hypothesis.

## Sixteen interfaces

| Interface | Binder/type result |
| --- | --- |
| SN1 `asProfile_prob` | `j : Fin D.K`, `l : Fin D.k`, and explicit `D` supply every index. `TimeProfile.prob` returns `ℝ`; `Riffle.prob` returns `NNReal`, so the explicit coercion on the right is necessary and correct. |
| SN2 `legalVector_digit` | The result of the vector is `Fin D.k`; `.val` and `Riffle.digit` are both natural numbers. The sole coordinate bound is exactly the conditional branch used by the vector. |
| SN3 `legalVector_legal` | `TimeProfile.LegalPrefix p X M` expects `p : Fin K → Simplex k`, `X : Fin K → Fin k`, and `M : ℕ`. The dimensions are `D.K`, `D.k` and `x.length` throughout. No legality of the padded suffix is requested. |
| SN4 `cL_prefix_eq` | Both sides are real. `TimeProfile.cL` argument order is `N p X b w M`; the candidate supplies `D.N`, `asProfile D`, the vector of `x`, `A.b`, `A.w.length`, `u.length`. `hux` yields the necessary upper endpoint bound from `hx.1`. There is no hidden need for an ambient-prefix premise in this exact sum equality. |
| SN5 `cL_parent_eq` | `Riffle.parent_length x` is exactly `(parent x).length = x.length - 1`, with natural truncated subtraction. The same encoded vector of `x` is used, and `parent_prefix x` supplies SN4's prefix premise. The empty-word case is included. |
| SN6 `sampleRow_full` | `TimeProfile.ShuffleSample (asCuts D)` is the dependent product over `Fin D.K` of column assignments on `Fin D.N` with alphabet `Fin D.k`. Thus `sampleRow sample i : Fin D.K → Fin D.k`. This is definitionally `Riffle.FullIndex D`, but it does not uniquely determine an entire model from just its `K`/`k` projections. The corrected explicit `Riffle.fullList (D := D)` resolves that issue. `Riffle.Full D` takes the resulting list word. |
| SN7 `expectedCount_eq_integral` | `TimeProfile.rowCount` takes two explicit arguments: `(rows : Fin N → Fin K → Fin k)` and `(B : (Fin K → Fin k) → Prop)`; its result is `ℕ`. `sampleRow sample` is the required row function, and the displayed predicate with explicit `fullList (D := D)` has exactly the required argument type. The entire row count is cast to `ℝ` before integration. `fixedCountMeasure (asCuts D)` is a measure on the same annotated sample type. No `E`-measurability binder is needed on this finite space. |
| SN8 `expectedCount_cylinder_eq` | `Riffle.Cylinder D u` is a `Set Riffle.Word`. The left NNReal expected count is cast to real. `TimeProfile.prefixMass` takes arguments `N p X M`, precisely as supplied. `u.length ≤ D.K` follows from `hux.length_le` and `hx.1`. |
| SN9 `expectedCount_piece_eq` | Membership `hx : x ∈ Riffle.Desc D A.w` reduces to a conjunction, with `hx.1 : Legal D x`. The piece event takes its final index as `ℕ`, so `j.val` on the left is correct. The numerical side mass takes the final index as `Fin D.K`, so `j` on the right is correct. Its argument order is `N p X w side j`. |
| SN10 `sideMaximum_eq` | **`Riffle.sideMaximum` returns `NNReal`; `TimeProfile.sideMaximum` returns `ℝ`.** The latter computes an NNReal finite supremum internally and coerces it in its definition. The explicit real coercion on the left, and no extra coercion on the right, give equality in `ℝ`. `hvx.length_le` and `hx.1.1` bound the index endpoint. Both empty suprema are zero. |
| SN11 `cFAt_eq` | Both sides have type `WithBot ℝ`. `TimeProfile.cF` argument order is `N p X w v`. The candidate supplies the ambient length then the selected prefix length, without reversing them. The same zero-side convention appears in both definitions. |
| SN12 `cF_eq` | `hx : x ∈ Desc D (join y z)` gives `hx.1 : Legal D x` and `hx.2 : join y z <+: x`. `rawPair_join_desc hp` gives the ambient prefix of the join, hence the ambient descent needed by SN11 and continuation. No terminality or finite-real-exponent binder is hidden in either conclusion type. |
| SN13 `rawPair_crossings` | `TimeProfile.Crossings` has parameters `p X w v chi` and no population parameter. The candidate follows that order. `hnt` is exactly the pair nonterminal condition needed to derive both individual nonterminal boundary conditions. All `Fin D.K` witness bounds come from existing legal lengths; no extra positive-depth or parent-length binder is required. |
| SN14 `stop_stableAt` | `StableAt` takes `N p X b w M F delta`. Its final proposition is the real non-strict inequality. The supplied `hF` is equality in `WithBot ℝ`, exactly the input type of `Riffle.stop_iff_sub_lt`. All scientific quantities remain those of the actual setup. |
| SN15 `gamma_parentCrossing` | The proof projection **`hx.1.1.1 : Riffle.Legal D x` is correct**, as expanded below. `ParentCrossing` takes `N p X b w v M F delta`, so the join length precedes `x.length`. `gamma_first_crossing` takes `hp`, then `hroot`, then `hx`, exactly as described. Its conclusions give `0 < M`, `v ≤ M-1`, and the parent non-Stop fact without extra premises. |
| SN16 `ambientApproximation_iff` | `AmbientApproximation` takes `N p X w r b eTime eMass`; the supplied order is `D.N p X A.w.length r A.b er eb`. The right expected count is coerced to real **inside** `Real.log`. `TimeProfile.logScale D.N` is definitionally `Real.log (D.N : ℝ)`. No sign or smallness premise on `er,eb` is required for this equivalence. |

For SN15 the exact conjunction nesting is:

```text
hx                    : x ∈ Gamma A y z
hx.1                  : x ∈ pairDesc A y z
hx.1.1                : x ∈ Desc D A.w
hx.1.1.1              : Legal D x
hx.1.1.2              : A.w <+: x
hx.2.1                : Stop A y z x
hx.2.2                : ¬Stop A y z (parent x)
```

No projection relies on a new structure field or a named theorem that is absent from the imports.

## Existing input declarations checked

The following exact names and required argument shapes were found in the current source and remain present in the compatible source where relevant:

- `TimeProfile.Cuts.profile_prob cuts hN j l` and `TimeProfile.Cuts.profile_pos_iff cuts hN j l`.
- `Riffle.digit_prefix hprefix hi`, `Riffle.parent_prefix x`, `Riffle.parent_length x`, `Riffle.fullList_length`, and `Riffle.fullList_digit` with its bound `i < D.K`.
- `TimeProfile.sample_entry_count_pos sample row j`; its conclusion is positive `cuts.count j (sampleEntry sample row j)`. `sampleRow` is definitionally the function of these entries.
- `TimeProfile.fixedCount_integrable cuts f` for an arbitrary real function on its finite sample space.
- `TimeProfile.expected_box_count cuts hN allowed`, where `allowed : Fin K → Finset (Fin k)`; this is an exact expected cardinality identity.
- `TimeProfile.expected_prefix_count cuts hN X M hMK`, with the actual required endpoint premise `M ≤ K`.
- `TimeProfile.expected_left_side_count cuts hN X j w hwj` and `TimeProfile.expected_right_side_count` with the identical binder pattern; the explicit premise is `w ≤ j.val`.
- `Riffle.pieceEvent_iff s hx hiw hix`, where `hx` is ambient descent, `hiw : A.w.length ≤ i`, and `hix : i < x.length`.
- `Riffle.cFAt_continuation hx hvx`, where `hx` is ambient descent and `hvx` a list prefix.
- `Riffle.rawPair_join_desc hp`, `Riffle.rawPair_prefix_join hp`, and `Riffle.boundary_nonterminal hboundary hlength_ne_K`.
- `Riffle.leftIndex_mem A i hiK`, `rightIndex_mem A i hiK`, `leftIndex_legal A i hiK`, and `rightIndex_legal A i hiK`; these use natural indices and the proof `i < D.K`.
- `Riffle.stop_iff_sub_lt hF` and `Riffle.not_stop_iff_sub_ge hF`, for `hF : cF A y z = (F : WithBot ℝ)`.
- `Riffle.gamma_first_crossing hp hroot hx`, with the crucial root-not-stopped argument included.
- `Riffle.admissiblePair_rawPair hpA` and `Riffle.stable_desc hp hxS` for later specialization to the actual profile-word domain.

The optional direct-weight alternative uses the real existing `Riffle.weight_eq_zero_of_not_legal`; its extra module import is noted above. No statement here relies on treating `TimeProfile.expected_cF_eq` as a cross-package identity. The analytical `source_*` theorems are not prerequisites of the sixteen finite interfaces, and no source specialization has been inserted.

The source-level binder audit is complete. Actual implementation, elaboration, compilation and trust verification remain for the post-freeze phase; no such new implementation was attempted during this review.
