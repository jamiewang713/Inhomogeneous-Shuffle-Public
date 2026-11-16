# Stable/numerical bridge implementation: independent algebra review

## Approval and identity

Approved the completed `FirstMomentModel/StableNumericalBridge.lean` against the frozen four definitions and SN1–SN16 in `STABLE_NUMERICAL_BRIDGE_CONTRACT.md`.

Reviewed implementation SHA-256:

`a1485441183054eba94a887919725e6da0bba49f549500a540c24526d4b3de7f`.

Frozen contract SHA-256:

`35ad29f0a886382ab06ca49e752fb854a2e702f5edc61f7a5d499b97f408980f`.

The source contains exactly four definitions and sixteen theorem declarations, with precisely the frozen names. I extracted each theorem signature from the completed source and compared it with its exact contract block: all sixteen agree after removal of whitespace alone. No binder, assumption, conclusion, coercion, or dependent proof argument was changed. I separately checked the four definition bodies against the frozen definitions.

Every dependency hash recorded under `sha256` in `STABLE_NUMERICAL_BRIDGE_FREEZE.json` still matches. A source token scan found no `axiom`, `sorry`, or `admit`. No extra public or private helper declaration was introduced; intermediate facts are local to the approved proofs. I made no source, compatibility-copy, or frozen-file edits.

The primary agent is independently running the full Lean compilation and kernel dependency verifier. This report is the independent mathematical/interface review of the completed source, not a substitute for that verifier.

## Definitions and initial comparisons

`asCuts` reads exactly the finite coordinates of `D.n`; its sum field follows by the finite alphabet reindexing and `D.sum_counts`. `asProfile` is exactly the already defined cut profile with positivity of `N` derived from `D.one_lt_N`. `legalVector` preserves each actual digit and pads only after the word's length with zero; the only bound for that padding is the existing `D.two_le_k`. `sideProbability` chooses the two existing strict-side probability sums.

SN1–SN3 do not claim that the padding is legal. The profile equality is the NNReal-to-real count ratio, actual digit agreement is restricted to `j.val < x.length`, and positive probability follows from the word's own positive-count clause.

SN4 explicitly uses `Finset.sum_bij` between `TimeProfile.positions` and the natural `Ico`. The inverse bound is derived from `u <+: x` and legality of `x`; the term equality uses both actual-vector agreement and `Riffle.digit_prefix`. Thus it neither truncates an out-of-range sum silently nor adds an ambient-prefix premise. When `u` is shorter than the ambient word both ranges remain empty. The reciprocal count ratios agree exactly, and `A.b` is retained. SN5 applies this same vector to the literal parent, including the empty-word natural-subtraction case.

## Literal expectation derivation: SN6–SN9

SN6 derives full sample-row legality from `sample_entry_count_pos`, the alphabet-valued sample entry, and the actual `fullList` length/digit facts. This is the necessary legal-row fact, rather than an assumption about arbitrary vectors.

SN7 contains the genuine finite expectation derivation:

1. Its local `B ω sample` is the cardinality of the singleton-coordinate box for the complete finite word `ω`.
2. `hB` rewrites that cardinality as the sum of indicators of exact row-vector equality. The converse to pointwise equality is proved by function extensionality.
3. `hcount` partitions every row indicator by its unique full vector and commutes the two finite sums. Membership in the arbitrary set `E` is tested only on the complete word represented by that vector.
4. `hexpected` applies the existing `TimeProfile.expected_box_count` to the singleton box and identifies its product with the coercion of `Riffle.weight` using SN1.
5. The final calculation uses pointwise equality of the count functions, finite integral linearity, and `TimeProfile.fixedCount_integrable` for each summand. It then recovers exactly the NNReal finite sum defining `Riffle.expectedCount`.

This proof does not assume independence between different rows, an external expected-mass identity, or a measurability premise on `E`. The entire relevant sample space is the existing finite fixed-count space. Illegal alphabet vectors simply have the box expectation dictated by their zero product weight; the proof does not declare them legal. Empty-column products and the unique empty full vector are included.

SN8 carefully separates two facts. Its raw-vector helper proves only that the list-prefix relation is equivalent to matching the encoded prefix coordinates. That statement is valid without full legality. The subsequent cylinder row-set equivalence is restricted to actual samples and inserts `sampleRow_full` explicitly in its reverse implication. Hence it does not make the false unrestricted equivalence between a cylinder event and coordinate matching on arbitrary illegal vectors. The length needed by `expected_prefix_count` is derived from the prefix and legality hypotheses.

SN9 follows the same discipline. The raw-vector helper is only a take-equality/coordinate-agreement equivalence. The ambient prefix is derived from agreement before `j`, `A.w.length ≤ j.val`, and `x` extending `A.w`. The actual sample event equivalence then uses `Riffle.pieceEvent_iff`, the established sample legality, and exact natural/Fin comparison of the digit at `j`. Only then does the proof identify the row set with `leftSideRows` or `rightSideRows` and apply the existing expected-side-count theorem. Later columns remain unrestricted, and no conditional law or variance statement is introduced.

## Finite suprema and extended exponents: SN10–SN12

SN10 proves the reindexed NNReal suprema equal by two inequalities. Its local `hterm` applies SN9 and cancels `Real.toNNReal` of the coercion of an NNReal expected count. For every natural `Ico` index it derives the corresponding `Fin K` bound from `v <+: x` and legality; in the reverse direction it sends each `positions` index to its natural value. `Finset.sup_le` and `Finset.le_sup` are applied to the corresponding members on each side.

The argument never commutes a random maximum with expectation. It also never assumes a nonempty index set. If `v.length ≤ A.w.length`, both suprema are zero, as required. An additional ambient-prefix assumption on `v` would be unnecessary and was not added.

SN11 rewrites both maxima by SN10 and unfolds the identical square roots and extended logarithms. The remaining equality is definitional. In particular the zero test and bottom value are preserved, including one-sided zero mass and empty maxima; a real `log 0` convention is not substituted for bottom.

SN12 derives ambient descent of `x` from the raw pair's join and the supplied continuation. It then uses the existing `cFAt_continuation` with the correct orientation before applying SN11. It does not assume nonterminality or a real representative of the exponent, so terminal and bottom cases remain included.

## Boundary and stopping conditions: SN13–SN16

SN13 retains exactly the frozen `RawPair`, nonterminality, and join-descendant inputs. Nonterminality supplies that neither boundary length is `K`, enabling `boundary_nonterminal` on both sides. The witnesses are exactly the natural final positions `y.length - 1` and `z.length - 1`; the proof derives their lower ambient bounds, strict boundary-length bounds, and finite-column bounds. Both witnesses lie strictly before the join length.

The left witness uses `leftIndex_legal` to form the finite digit and `leftIndex_mem` to obtain probability at least `A.chi`. Prefix agreement and SN2 carry the genuine crossing to the vector digit. A single nonnegative summand then bounds `leftProbability` below. The right proof symmetrically uses `rightIndex` and the reversed strict comparison. No budget, retention-only inference, full-support assumption, or additional crossing hypothesis appears.

This is a deterministic side-mass crossing result. In particular including an early deterministic column in the source boundary definition does not turn this theorem into an anti-concentration assertion. Terminal fallback boundaries are excluded by the stated nonterminal premise; SN12 continues to cover their exponents separately.

SN14 translates the actual `Stop` premise by the original strict stopping equivalence and the exact cost equality, then uses strict-to-nonstrict implication for `StableAt`. It does not replace `Stop` by bare `Stable` membership or assert a converse. The finite representative equation `hF` remains explicit.

SN15 retains the root-not-stopped premise and invokes `gamma_first_crossing`. Its strict length conclusion provides the first two `ParentCrossing` clauses, and the theorem's parent non-Stop conclusion is translated by `not_stop_iff_sub_ge` and the same-vector parent cost identity. The dependent legality argument is exactly `hx.1.1.1`, as frozen. No terminal exclusion or extra parent condition was silently assumed.

SN16 rewrites the literal ambient cylinder expectation using SN8 and then closes by the definitions. It leaves `r`, `er`, and `eb` arbitrary, does not prove an approximation from bare `Setup`, and does not replace `A.b` by an exact mass exponent.

## Remaining scope

The module proves the finite representation and expectation bridges that were frozen. It preserves zero piles, `K=0`, empty ranges, terminal pairs, and extended-real bottom. It does not claim the source horizon relation, time-profile approximation, small error budgets, regularity, or a variational margin from these finite model fields. Those are still supplied by their proper source interfaces.

No issue was found in the completed implementation. The previously identified stochastic endpoint density/localization obstruction is outside these sixteen theorems and is not hidden by any of their conclusions.
