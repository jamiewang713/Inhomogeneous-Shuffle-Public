# Independent final review of the occupancy-conditioning implementation

Reviewer: statements agent. This is a new final addendum to the historical static review in `conditional_implementation_statements.md`; that earlier review and every frozen document remain unchanged.

## Reviewed versions

The frozen conditional contract still has SHA-256 `0790d840b1e1fc25f496672fedf6c68a6e76b99961e0173e6478cc0761e71689`.

| File | SHA-256 |
| --- | --- |
| `EdgeLocalization/Conditional/Model.lean` | `3234668ca977af586e5551ad116cc6ef3c3ae63c98846fa35a39a64f11104bc4` |
| `EdgeLocalization/Conditional/Split.lean` | `ae25208eab9afd983de656c9dad501baf1cd0744da7829d6ad93b93517b4a989` |
| `EdgeLocalization/Conditional/Counts.lean` | `f97c5abefa71d4c34634113e9a0cdba6b9004644a260d0281f45705f2a189991` |
| `EdgeLocalization/Conditional/Estimates.lean` | `a67f3ceeb5865f8ec52563712688387e75a8dd5a4693be6bda7a2d84e1e73df6` |

These hashes match the successful root verification record dated `2026-09-17T21:43:01.937241+00:00`.

## Independently confirmed elaboration correction

The initial O.06 proof timed out while elaborating the first step of its final calculation. Instrumentation in a temporary copy confirmed that all preceding local proofs, including `hz`, `hsplit`, `hprob`, and `hinner`, had completed. Restricting the final simplification alone did not resolve the timeout. Removing the local `classical` command alone also did not resolve it.

Changing that calculation step from `:= hsplit _` to `:= by exact hsplit _` lets the expected equality determine the unspecified function before elaborating the application. I independently compiled a temporary copy with this change at 200,000 heartbeats. A further test showed this expected-type change alone already compiled the whole file at that limit; the old broad final simplification produced only a linter warning.

The accepted project version additionally uses explicit true/false branches and `simp only` for the final indicator algebra. This is a proof-only elaboration correction. It changes no quantifier, assumption, definition, conclusion, or intermediate mathematical estimate. The project version has no raised heartbeat option, and I independently compiled the current `Conditional/Estimates.lean` successfully with no diagnostics.

## Final signature and mathematical review

All seven declarations and the three definitions retain the exact frozen signatures and meanings.

- **O.01, `matrix_expectation_split`:** `f` is an arbitrary real-valued function. No sign, boundedness, positive-probability, or new independence assumption is present. The prefix and suffix histogram equalities are derived from `hn`; both laws retain the original population `N`. The equivalence of sample spaces and uniform weights prove the finite sum identity.
- **O.02, `tailCollisionFactor_suffix`:** the scalar identity has explicit `N` and no `hn`. The suffix reindexing covers precisely the columns at indices at least `M`, including an empty suffix.
- **O.03, `prefix_occupancy_glue`:** the statement has no `hn`. Its proof establishes membership equivalence for each row label before taking cardinalities, using the literal restriction map of `splitMatrix`.
- **O.04, `increasing_pairs_in_finset_card`:** the input is an arbitrary finite set of natural numbers. The order equivalence with its rank indices proves the binomial count; no interval or consecutive-label hypothesis is introduced.
- **O.05, `tail_expected_collisionPairs_given_prefix_array`:** the prefix array is arbitrary and fixed. The code proves local prefix coordinate and suffix coordinate identities, then pointwise prefix membership and the equivalence of full-row equality with suffix-row equality for two labels in the fixed prefix subset. It does not infer those facts from occupancy cardinality alone. The candidate-pair set contains exactly the increasing pairs from that subset. Each such pair receives the original-`N` tail collision factor, and O.04 counts the pairs. The proof explicitly handles `N = 0` and `N = 1` before the general pair calculation. Sorted collision cardinality is transferred to raw rows by the previously proved permutation invariant.
- **O.06, `matrix_collisionPairs_occupancy_slice`:** both the stated indicator and stated probability use sorted full-matrix occupancy. The local equality `hz` transports that occupancy to raw prefix-array occupancy for every prefix/suffix realization. The same equality is used in both the collision integral and the slice probability. O.05 supplies the inner expectation, and explicit indicator branches supply the finite sum algebra. Every `q : ℕ` remains quantified, with no hypothesis that its slice is nonempty or has positive probability and no division by that probability. Thus null slices, including impossible `q > N`, are included.
- **O.07, `matrix_internal_edges_occupancy_slice`:** the indicator is exactly the same sorted occupancy event. Pointwise internal-edge cardinality is bounded by collision-pair cardinality on the true branch; the false branch is zero. Expectation monotonicity and O.06 prove the bound without identifying edges with collision pairs.

The definitions `prefixCounts`, `suffixCounts`, and `splitMatrix` also retain their frozen explicit/implicit argument order. No histogram-sum premise has been added to the split definition, no conditional distribution has been stored as an assumption, and no post-freeze named helper has been introduced.

## Kernel and dependency verification

I independently ran the current `Conditional/Estimates.lean` through Lean 4.24.0 and re-ran `audit/PrintConditionalAssumptions.lean`; both returned exit status zero. All seven theorem declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Of the three definitions, `prefixCounts` has no axiomatic dependencies, `suffixCounts` uses only `propext` and `Quot.sound`, and `splitMatrix` uses only the same three standard axioms as the theorems.

The root verifier additionally records all seven frozen theorem names, exactly the three planned definitions, no prohibited proof tokens, unchanged frozen contracts and source material, unchanged earlier implementations, and a successful dependency build. The printed signatures agree with the frozen inventory; this review does not infer semantic agreement merely from successful compilation.

**Acceptance:** no remaining issue was found in this conditional addendum. This certifies the exact finite occupancy-slice collision identity and internal-edge bound only. It does not assert that the full edge-localization goal or the obstructed spatial density claims have been formalized.
