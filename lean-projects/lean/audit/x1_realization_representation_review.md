# Representation review: concrete frozen X1 realization

Reviewed `X1_REALIZATION_DRAFT.md` against the frozen X1/F3 targets and the existing `FixedColumns`, `AmbientCounterexample`, `Conditioning`, and `ConditionalHypergeometric` interfaces. This is a read-only implementation review; no Lean definitions or proofs were changed.

**Decision:** approve R1–R4. They instantiate the two frozen experiments and positive-event conditioning. They do not add a reserve hypothesis, assert nonzero variance, or generalize the exported counterexample to arbitrary middle size.

## Definitions and binders

The amended draft explicitly fixes `singleton = true` to mean middle size `1` and `singleton = false` to mean middle size `L`. Definitions may be total at `L = 0`, but the exported X1 conclusions retain the frozen `hL : 1 ≤ L` binder. Use `d : ℕ` and `Fin (d + 2)` for the column index. The fixed histogram itself supplies legal-column nonemptiness; no extra `Nonempty`, positivity, or population feasibility assumption is needed.

Use the existing `Histogram (Fin (2 * L + middleSize)) 3`, `FixedColumn`, and `fixedMatrixLaw` constructions. Its histogram counts can be specified by `if a = 1 then middleSize else L`, with the three-entry total proved. The concrete sample space is a function from `Fin (d + 2)` to that fixed-column type. The law is the existing product of uniform column laws.

The first column is the coordinate `0`. On its row labels define middle rows by digit `1`, residual rows by digit different from `1`, marked rows by digit `0`, and sample rows to be exactly residual rows. Define `leftCount` and `throughCount` by the cardinalities of the filters for digit `< 1` and digit `≤ 1`. These are cumulative counts. Any one-based position convention needs its explicit deterministic shift and must not silently replace the count variable in a hypergeometric law.

The amended R1 includes the bookkeeping identity

`(markedRows ω ∩ sampleRows ω).card = leftCount ω`

in its realization. This follows from the definitions and shows that the actual sampled marked count is the variable whose conditional law appears in R2. The actual parameter cardinalities then equal population `2 * L`, marked `L`, draws `2 * L`, hence `exhaustedParams L`. No new sampling-uniformity claim is needed when the sample equals the full population.

## Individual target review

| ID | Representation and premise review |
| --- | --- |
| R1 | The legal-column field gives the three exact digit counts for every matrix. Finite filter partitions give the residual size and endpoint sums. Retain `hL`; no additional premise on the matrix or middle size is needed. The sampled marked count equals `leftCount` pointwise. |
| R2 | Quantify over an arbitrary event on the explicit matrix space with `hE : 0 < law.prob E`. State equality with `(exhaustedParams L).pointMass q` for **every** `q : ℕ`, so support outside the finite hypergeometric range is included. Pointwise constancy gives that equality directly. Existing conditional-count-law transport then supplies mean and variance; the right cumulative count has its unit atom at `L + middleSize`. This does not say that an arbitrary positive event preserves uniformity of the remaining assignments. |
| R3 | Treat `S` as any predicate on matrices. Under the same positive `E`, the event conjunction is pointwise equal to `S`, so the stated conditional probabilities agree. Do not assume `S` is conditionally likely merely because it is unconditionally likely. The identities are valid whether or not the manuscript eventually supplies a separate meaning for “retained.” The added finite-tower consequence is also approved: for any finite-valued `Z` and real `b`, its assumed sum bound on every positive atom gives `P(S \| Z=z) ≤ b/2`; `total_probability_bound` with the constant bound `b/2`, followed by the sum of reveal probabilities being one, yields `2*P(S) ≤ b`. No premise `0 ≤ b` is necessary. Null atoms contribute zero. |
| R4 | The actual reveal is the finite-set-valued middle-row map. An atom is the predicate `middleRows ω = R`; require its probability to be positive, then apply R2. Additional finite revealed information may be conjoined into a positive event and is already covered by R2. The complement computation uses the actual residual and sample cardinalities, with `hL` supplying a nonzero denominator. Both residual categories have cardinality `L > 0`. There is no conditional law on a null fibre. |

## Minimal public interfaces

The public conclusions should depend only on the experiment parameters `singleton : Bool`, `L d : ℕ`, the retained frozen hypothesis `hL : 1 ≤ L`, and, where relevant, an event/reveal atom with its explicit positive-probability proof. R1 additionally takes a legal matrix; R2/R3 take events on that matrix space; R4 takes a finite set of row labels. The finite-tower consequence additionally takes a finite-valued reveal `Z`, a real bound `b`, and the explicit proposed conditional sum bound that it assesses. No separate bounds on digit counts, sample size, variance, conditional support, or integrability belong in the statements: each follows from the fixed finite construction.

For R2, the existing `FiniteLaw.HasConditionalHypergeometric law E leftCount (exhaustedParams L)` proposition is an exact interface, since it means equality of all natural point masses. The numerical corollaries use the same `hE` and can reuse `conditional_hypergeom_expect`, `conditional_hypergeom_variance`, and the full-draw facts. A direct deterministic proof is equally faithful.

## Remaining boundary of the source claim

This construction realizes the finite D6 product experiment, actual first-column reveal, residual population, complete sample, and cumulative first-prefix counts. It does not by itself formalize the manuscript's complete exploration process, its named one-based endpoint functions, crossing and stopping rules, admissible or stable prefix predicates, fluctuation-regularity conditions, the hierarchy of asymptotic parameters, or the meanings and uniformity of `o(1)` and `O(δ)`. `Fin (d + 2)` ensures a later column exists but is not a proof of every manuscript nonterminal condition. Those source predicates require exact frozen definitions before a theorem may claim the counterexample satisfies them. The draft's explicit boundary accurately preserves this distinction.

## Final compiled-statement review

Reviewed the completed `Shuffle/AmbientMatrixCounterexample.lean` against the immutable `FROZEN_X1_REALIZATION.md`. **No R1–R4 target is missing and no frozen premise was changed.** This review changed no Lean source file.

- R1 is supplied by `counts` and `residual_intersection`. `residualRows` is the literal complement of `middleRows`; `sampleRows` is definitionally that full residual set. `residualCount` is the actual marked/sample intersection cardinality and is proved equal to `leftCount`. The residual unmarked cardinality is also exactly `L`.
- R2 is supplied by `conditional_left_law`, `conditional_residual_law`, `conditional_left_mean`, `conditional_left_variance`, and `conditional_unit_atoms`. The law equality covers every natural count, and the conditioning event has explicit positive probability. The variance is centered under the actual conditioned matrix law.
- R3 is supplied by `conditional_restricted_counts` and `retained_bound_forces_small_probability`. The latter has the exact proposed bound on every positive atom of any finite reveal and concludes `2 * P(S) ≤ b`, with no extra sign condition on `b` or conditional-likelihood hypothesis on `S`.
- R4 is supplied by `middle_reveal_residual_law` and `actual_sample_exhausts`. R2's arbitrary-event corollaries specialize directly to the same positive middle-row atom, so its means, variance, and unit atoms need no new hypotheses. The exhausted sample fraction uses actual row-set cardinalities and derives its nonzero denominator from `hL`.

All exported X1 conclusions retain `1 ≤ L`, even where a stronger private identity is available. The Boolean selects only the two frozen middle sizes. Both public endpoint variables remain the frozen zero-based cumulative counts. No theorem identifies these counts with an unformalized manuscript endpoint function or asserts uniformity of residual assignments under arbitrary conditioning.

The `law` definition's `convert` transports `fixedMatrixLaw` between equal `Fintype` instances arising from different decidable-equality choices. Inspecting the generated equality proof confirms that the underlying sample type is unchanged. A separate, successful Lean stdin check proved for every matrix `ω` that its mass under `law` is exactly the product of the uniform column masses. That check used only `cast_heq`, subsingleton equality of `Fintype` instances, and mass projection, so it verifies that the transport does not alter any product weight.

`#print axioms` for the law and all new public proof families reported only `[propext, Classical.choice, Quot.sound]`. The explicit source-formalization boundary above remains applicable.
