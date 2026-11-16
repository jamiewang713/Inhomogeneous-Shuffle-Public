# Stable/numerical adapters: independent implementation audit

**Verdict: approve the completed four definitions and SN1–SN16. No interface correction or missing premise was found.** Final approval was withheld until the coordinator's full-module completion notice and then checked against the stable source snapshot below.

- Frozen contract: `STABLE_NUMERICAL_BRIDGE_CONTRACT.md`, SHA-256 `35ad29f0a886382ab06ca49e752fb854a2e702f5edc61f7a5d499b97f408980f`.
- Implementation: `FirstMomentModel/StableNumericalBridge.lean`, SHA-256 `a1485441183054eba94a887919725e6da0bba49f549500a540c24526d4b3de7f`.

This is an independent source/interface and adversarial proof review. The coordinator reports the module compiles and is separately running the kernel/foundation verifier. I did not duplicate that active build and do not report its unfinished result as completed. No code, contract, or prior frozen report was edited.

## Inventory and interface preservation

The file has exactly the four frozen definitions, in the prescribed namespace, and exactly sixteen exported theorems. All auxiliary maps, event equivalences, finite sums, and comparison facts are local to proofs. The definition fields are literal: `asCuts` reads the original natural counts; `asProfile` normalizes them by the original `N`; `legalVector` copies each actual prefix digit and pads only the suffix with zero; `sideProbability` selects the original left/right sum.

| Interfaces | Review result |
|---|---|
| SN1–SN3, lines 36–52 | Exact probability coercion and prefix-digit/legality conclusions, with unchanged binders. Only the actual legal prefix is claimed positive. |
| SN4–SN5, lines 54–86 | Exact cost identities. No ambient-prefix premise was added to SN4; SN5 keeps the same vector and handles the empty parent through natural subtraction. `A.b` is unchanged. |
| SN6, lines 88–97 | Actual sampled rows are full legal Riffle words; the explicit `(D := D)` annotation is present. |
| SN7, lines 99–172 | Exact general-set expectation identity, with arbitrary `E` and no measurability or legality restriction added. |
| SN8–SN9, lines 174–308 | Cylinder and side-piece expectations match the original events with exactly the frozen legality/prefix/index hypotheses. |
| SN10–SN12, lines 310–360 | Exact finite maxima and extended-fluctuation identities, including empty/zero maxima and terminal pairs. No positivity or nonterminal premise was added. |
| SN13, lines 362–417 | Actual crossing witnesses derived from the frozen nonterminal raw-pair premises. No retained, admissibility-budget, or finite-fluctuation premise was added. |
| SN14, lines 419–426 | Strict source Stop implies the relaxed numerical StableAt inequality, using the given representative of cF. No converse is asserted. |
| SN15, lines 428–437 | The essential root-not-stopped premise is retained. ParentCrossing uses the actual parent and exact Gamma legality projection. No separate nonterminal premise was added. |
| SN16, lines 439–448 | Literal ambient-approximation equivalence, with unrestricted real errors and original free `A.b`; no approximation or exact mass equality is assumed. |

## General-set expectation proof

SN7's local `B omega sample` is the number of rows in the complete singleton-coordinate box specified by `omega`. The proof first identifies this count with a sum over labelled rows of the indicator that their whole row vector equals `omega`. Its local `hcount` then partitions the arbitrary `E`-row count over **all** complete finite words, summing only those whose `fullList` lies in the fixed set `E`.

This partition is exact and pointwise. It does not assume that every alphabet-valued word is a realizable row; impossible words simply have an empty box and zero product mass. It also does not assume independence of different rows. The proof applies the already proved `TimeProfile.expected_box_count` to each singleton box, identifies its product mass with `Riffle.weight` by SN1, and interchanges only a finite sum and integral. Integrability is supplied by `TimeProfile.fixedCount_integrable` for the actual fixed-count sample measure. The final finite distributivity and NNReal coercions recover exactly `Riffle.expectedCount`.

No event-measurability hypothesis on an arbitrary set of lists is hidden: the integrated function has a finite sample domain. `E` need not consist of full or legal words. At `K=0`, the complete-word index has one empty function, and the same partition gives either `N` or zero as required.

## Sample legality and prefix/side correspondence

SN6 derives positivity of each sampled digit's pile directly from `TimeProfile.sample_entry_count_pos`; the sample's own occurrence witnesses that positive count. It uses `fullList_length` for the terminal length. Thus it does not silently transfer iid-row or homogeneous-model facts.

SN8 proves a local prefix-coordinate equivalence for arbitrary raw finite vectors. This is legitimate because it compares **prefixes**, not the extra full-legality predicate in a cylinder. In the actual cylinder-row identity, the proof uses SN6 to add that full-legality predicate specifically for sampled rows. The reverse prefix implication checks `u.length≤K` and proves list-element equality at every actual prefix coordinate. The arbitrary zero-padded suffix of `legalVector` is never used in that comparison.

SN9 likewise proves equality of the first `j` coordinates with `x.take j`. Its ambient-prefix implication is derived from `A.w<+:x` and `A.w.length≤j`, rather than assumed as an extra event. The sampled-row event uses `pieceEvent_iff`, SN6, and the actual smaller/larger digit at `j`. The right-hand side fixes only earlier coordinates and the side comparison; **all later coordinates remain unrestricted**. Hence this is the intended side family, not an incorrectly fixed continuation cylinder. Final-coordinate side pieces are included because only `j<K` and `j<x.length` are used.

## Finite maxima and extended logarithms

SN10's local `hterm` rewrites each TimeProfile side mass by SN9 to the real coercion of a nonnegative Riffle expected count. Applying `Real.toNNReal` then returns that exact original NNReal value. Thus there is no unjustified cancellation at negative mass.

The proof compares the two NNReal finite suprema in both directions using `Finset.sup_le` and `Finset.le_sup`, with the explicit lift `i ↦ ⟨i,i<K⟩` or projection `j ↦ j.val`. The upper bound `i<K` comes from the prefix length and legality. This argument needs no nonempty index set and retains the correct zero default when `v.length≤A.w.length`. It never interchanges maximum and expectation.

SN11 then rewrites the two square-root arguments and uses the literal equality of the extended-log definitions. No logarithm positivity or finite-cF premise is introduced, so `⊥` is preserved. SN12 uses the already proved `Riffle.cFAt_continuation` and derives ambient descent from `rawPair_join_desc`. Its equality is valid even for terminal fallback pairs with one zero side.

## Crossing and branch premises

SN13 takes the two last crossing indices from `boundary_nonterminal`. Their membership in `[A.w.length,join.length)` is proved, and the actual selected digits are transported along boundary-to-join-to-word prefixes. Each probability side sum contains the corresponding extreme large-pile digit, whose mass is at least `A.chi` by `leftIndex_mem` or `rightIndex_mem`. Positivity of the remaining summands justifies the sum comparison. This is a side-mass witness only; no conditional variance claim is made.

SN14 uses `stop_iff_sub_lt` and then `.le`, so the original strict stopping test is preserved. SN15 uses `gamma_first_crossing hp hroot hx` to prove the strict join/word length inequality; natural arithmetic gives both `0<length` and `join.length≤length-1`. The parent non-Stop field is converted by `not_stop_iff_sub_ge` after SN5. The root-not-stopped condition was not dropped, so the earlier counterexample with Gamma membership at the join itself does not apply.

SN16 rewrites only the ambient cylinder's expected mass using SN8. It retains the complete logarithmic discrepancy from `A.b` and the actual time discrepancy. There is no horizon equation, error-sign premise, replacement exponent, homogeneous cutoff, or new parameter relation in this file.

## Trust and scope

The static scan found no `axiom`, `sorry`, `admit`, `unsafe`, `partial`, `implemented_by`, opaque declaration, or extra exported helper. This direct-source scan is distinct from the coordinator's transitive foundation audit.

The completed module provides genuine exact adapters to fixed-count expectations and the finite numerical definitions. It does not identify side means with conditional variances, exclude terminal fallback without the separately required source analytic inputs, prove localization, or resolve the false printed large/small density intermediates. No such claim is smuggled into an interface or proof.

All four definitions and SN1–SN16 agree with the frozen contract at the reviewed source hash. No correction is requested.

