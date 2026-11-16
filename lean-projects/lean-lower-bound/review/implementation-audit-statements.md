# Independent implementation audit by the Lean-statement reviewer

The reviewer compared `RiffleLower/Sorting.lean`, `Profiles.lean`, and `Cold.lean` directly against frozen contract v1 in `FREEZE.md` after implementing and kernel-checking the separate fixed-column moment module.

* **S1–S4:** every definition and quantified hypothesis agrees with the freeze. The output is exactly `Tuple.sort f`; equal-key counts refer to original labelled rows; the exact sorted fiber starts at `lowerRank`; the run event is contiguous and zero-based. S4 retains `1≤m` and `m≤keyCount`; its proof does not replace complete keys with proper prefixes. It makes no probabilistic claim.
* **D1a–D4:** time-cell-digit counts and all partition identities match the freeze. D2 is an exact product regrouping for arbitrary real representatives. D3 assumes positivity only for the selected factors and states the precise logarithmic identity. D4 carries exactly the frozen nonnegative-factor and coordinatewise-maximality hypotheses. No representative-cell approximation or integral limit is silently used.
* **C1–C3b:** the six real arguments and all exponent definitions match the freeze; C1 is solely algebraic. C2 assumes exactly `localizedKeys` and constructs one injective adjacent-edge witness per repeated complete key. It neither assumes an occupancy estimate nor claims probabilistic localization. C3 uses stable tie order to give precisely the frozen edge inclusion and cardinality bound.

No additional top-level mathematical helper was introduced in these three modules. Their auxiliary inequalities and finite injections are local proof steps. No extra sign, positivity, finite-size, regularity, independence, or concentration hypothesis appears. No `axiom`, `sorry`, `admit`, or `native_decide` declaration appears in the inspected project modules.

Audit result: **approve the implemented S/D/C statements and their correspondence to frozen contract v1**. This is not approval of the excluded full asymptotic cold-spot theorem.

The reviewer’s own `FixedColumns.lean` has kernel-checked proofs of every M01–M15 statement. The final version uses a namespace-local classical decidability instance; M02 and M05 export no additional decidability parameters. All zero-pile cases and the empty-time case remain included. Its final object file was compiled to `.lake/build/lib/lean/RiffleLower/FixedColumns.olean`.

## Independent audit of the integrated finite endpoints

The reviewer also read `RiffleLower/LowerBounds.lean` against frozen L01/L02. `inverseShuffle` is stable sorting of the lex-tagged **complete** row words, and `shuffleLaw` is exactly the finite pushforward of the concrete independent-column sample law. L01 preserves `N≥2`, `1≤m≤N`, and the strict real inequality `m<wordMean`; its false-positive penalty is exactly `(N-m+1)/m!`. Its proof supplies the observable run event from the proved occupancy bound and S4.

L02 preserves all frozen typical-environment hypotheses, with common `N,K,k,m`, nonnegative errors, a typical-set probability bound, and the exact per-environment mean/error inequalities. It builds one increasing-run event on permutations and averages that event's success probability, so there is no invalid averaging of TV distances and no unadvertised temporal-independence condition on the environment law. No new cutoff, entropy, local-good-shuffle, or asymptotic assumptions enter either endpoint.

Audit result: **approve the implemented L01/L02 statements and their proof dependencies against frozen contract v1**.
